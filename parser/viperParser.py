#!/usr/bin/env python3.6

import sys
import ast


class ParserException(Exception):
    pass


def parse(code):
    o = ast.parse(code)
    # todo fix those
    # decorate_ast_with_source(o, code)
    # o = resolve_negative_literals(o)
    return o.body


def astToString(node):
    nodeType = type(node)
    if nodeType == ast.Expr:
        return astToString(node.value)
    elif nodeType == ast.Call:
        return "Call(" + node.func.id + ", [" + astListToString(node.args) + "] )"
    elif nodeType == ast.Str:
        return "\"" + node.s + "\""
    else:
        raise RuntimeError("ast as something else:" + str(node))


def astListToString(nodeList):
    rez = ""
    for node in nodeList:
        if rez != "":
            rez += ", "
        rez += astToString(node)
    return rez


#    syntax BaseType      ::= "%bool"
#                           | NumericType | "%num256"  | "%signed256"
#                           | "%bytes32" | "%address"
def parseBaseType(name):  # value is Str. NumericType not yet supported
    if type(name) == ast.Name:
        return "%" + name.id
    else:
        raise ParserException("BaseType parsing not yet implemented for: " + str(id))


# syntax MappingType   ::= "%mapT"    "(" Type "," BaseType ")"
#
# example:
#   %mapT(%num256, %address)
def parseMappingType(param):
    return "%mapT(" + parseType(param.value) + ", " + parseType(param.slice.value) + ")"


#     syntax Type          ::= "%void"
#                           | BaseType
#                           | ByteArrayType
#                           | ListType
#                           | MappingType
#                           | StructType
def parseType(param):
    if param is None:
        return "%void"
    elif type(param) == ast.Name:
        return parseBaseType(param)
    elif type(param) == ast.Subscript:
        return parseMappingType(param)
    else:
        raise ParserException("Type parsing not yet implemented for: " + str(param))


# EventParam ::= "%eparam" "(" Id "," Type "," Bool /*indexed?*/ ")"
# example:
#   _from: indexed(address)
#   =>
#   %eparam(_from, %address, true)
def parseEventParam(key, value):  # value is Call
    rez = "%eparam(" + key.id + ", "
    if type(value) == ast.Call and value.func.id == "indexed":
        rez += parseType(value.args[0]) + ", true)"
    elif type(value) == ast.Name:
        rez += parseType(value) + ", false)"
    else:
        raise ParserException("Unsupported EventParam format: " + str(key) + " -> " + str(value))
    return rez


def parseEventParams(params):  # arg is ast.Dict
    rez = ""
    for i in range(0, len(params.keys)):
        key = params.keys[i]
        value = params.values[i]
        if rez != "":
            rez += " "
        rez += parseEventParam(key, value)
    return rez


# syntax Event    ::= "%event" "(" Id "," EventParams ")"
# syntax Events ::= List{Event, ""}
def parseEvent(node):  # node.annotation is ast.Call
    return "  %event(" + node.target.id + ", " + parseEventParams(node.annotation.args[0]) + ")"


#    syntax Global   ::= "%svdecl" "(" Id "," Type "," Visibility ")"
#    syntax Globals  ::= List{Global, ""}
#
# example:
#   %svdecl(balances, %mapT(%num256, %address), %private)
def parseGlobal(node):
    return "  %svdecl(" + node.target.id + ", " + parseType(node.annotation) + ", %private)"


#    syntax Decorator  ::= "%@constant" | "%@payable" | "%@internal" | "%@public"
#    syntax Decorators ::= List{Decorator, ""}
def parseDecorator(name):
    return "%@" + name.id


def parseDecorators(decorator_list):
    rez = ""
    first = True
    for decorator in decorator_list:
        if first:
            first = False
        else:
            rez += " "
        rez += parseDecorator(decorator)
    return rez


def parseParams():
    return ""  # todo


#    syntax Var      ::= "%var"      "(" Id ")"
#                      | "%svar"     "(" Id ")"
#                      | "%mem"      "(" Var "," Id   ")"  // struct field access
#                      | "%listelem" "(" Var "," Expr ")"  // list element
#                      | "%mapelem"  "(" Var "," Expr ")"  // map element
#
# examples:
#   %var(_value)
#   %svar(balances)
#   self.balances[_sender]  =>  %mapelem(%svar(balances), %var(_sender))
def parseVar(var):
    if type(var) == ast.Name:
        return "%var(" + var.id + ")"
    elif type(var) == ast.Index:  # same as ast.Name
        return parseVar(var.value)
    elif type(var) == ast.Attribute and var.value.id == "self":
        return "%svar(" + var.attr + ")"
    elif type(var) == ast.Subscript:
        return "%mapelem(" + parseVar(var.value) + ", " + parseExpr(var.slice) + ")"
    else:
        raise ParserException("Unsupported Var format: " + str(var))


# Only ReservedFunc at the moment
#    syntax ReservedFunc  ::= "%as_num128"    "(" Expr ")"
#                           | "%as_num256"    "(" Expr ")"
#                           | "%as_wei_value" "(" Expr "," Id   ")"
#                           | "%num256_add"   "(" Expr "," Expr ")"
#                           | "%num256_sub"   "(" Expr "," Expr ")"
#
# example:
#   %as_num256(%msg.value)
#
#   num256_add(self.balances[_sender], _value)
#   =>
#   %num256_add(%mapelem(%svar(balances), %var(_sender)), %var(_value))
def parseCallExpr(expr):
    if expr.func.id == "as_num128" or expr.func.id == "as_num256":
        return "%" + expr.func.id + "(" + parseExpr(expr.args[0]) + ")"
    elif expr.func.id == "as_wei_value":
        raise ParserException("todo unsupported")
    elif expr.func.id == "num256_add" or expr.func.id == "num256_sub":
        return "%" + expr.func.id + "(" + parseExpr(expr.args[0]) + ", " + parseExpr(expr.args[1]) + ")"
    else:
        raise ParserException("Unsupported Call expression format: " + str(expr))


# syntax ReservedExpr  ::= "%msg.sender" | "%msg.value" | "%msg.gas"
#                        | "%block.difficulty" | "%block.timestamp" | "%block.coinbase" | "%block.number"
#                        | "%block.prevhash"
#                        | "%tx.origin"
def parseReservedExpr(expr):
    return "%" + expr.value.id + "." + expr.attr


#    syntax Expr     ::= Const
#                      | Var
#                      | ReservedExpr
#                      | ReservedFunc  // expr dispatch table
#                      | "%self"
#                      | "%binop"     "(" BinOp     "," Expr "," Expr ")"
#                      | "%compareop" "(" CompareOp "," Expr "," Expr ")"
#                      | "%boolop"    "(" BoolOp    "," Expr "," Expr ")"
#                      | "%unaryop"   "(" UnaryOp   "," Expr ")"
#                      | "%icall"     "(" Id        "," Exprs ")"  // internal contract call
#                      | "%ecall"     "(" Id        "," Exprs ")"  // external contract call
#
# examples:
#   %var(_sender)
#   %as_num256(%msg.value)
#   %msg.value
#   %mapelem(%svar(balances), %var(_sender))
def parseExpr(expr):
    if type(expr) == ast.Name or type(expr) == ast.Index or type(expr) == ast.Subscript \
            or (type(expr) == ast.Attribute and expr.value.id == "self"):
        return parseVar(expr)
    elif type(expr) == ast.Attribute:
        return parseReservedExpr(expr)
    elif type(expr) == ast.Call:
        return parseCallExpr(expr)
    else:
        raise ParserException("Unsupported Expr format: " + str(expr))


# syntax Stmt     ::= VarDecl  // annotated assign
#                      | "%assign"    "(" Var "," Expr ")"
#                      | "%augassign" "(" AugAssignOp "," Var "," Expr ")"
#                      | "%if"        "(" Expr "," Stmts "," Stmts ")"
#                      | "%if"        "(" Expr "," Stmts ")"
#                      | "%for"       "(" Id "," Int "," Stmts ")"
#                      | "%for"       "(" Id "," Expr "," Expr "," Stmts ")"
#                      | "%break"
#                      | "%pass"
#                      | "%return"
#                      | "%return"    "(" Expr ")"
#                      | "%assert"    "(" Expr ")"
#                      | "%throw"
#                      | "%log"       "(" Id "," Exprs ")"
#                      // stmt dispatch table
#                      | "%send"      "(" Expr  "," Expr ")"
#                      | "%selfdestruct" "(" Expr ")"
#
# examples:
#   _value = as_num256(msg.value)
#   =>
#   %assign(%var(_value), %as_num256(%msg.value))
#
#   log.Transfer(0x0000000000000000000000000000000000000000, _sender, _value)
#   =>
#   %log(Transfer, %hex("0000000000000000000000000000000000000000"), %var(_sender), %var(_value)))
def parseStmt(stmt):
    if type(stmt) == ast.Assign:
        return "\n    %assign(" + parseVar(stmt.targets[0]) + ", " + parseExpr(stmt.value) + ")"
    else:
        return "\n    "  # todo temp to see results
        # raise ParserException("Unsupported Stmt format: " + str(stmt))


# syntax Stmts    ::= List{Stmt, ""}
def parseStmts(body):
    rez = ""
    for stmt in body:
        rez += parseStmt(stmt)
    return rez


#    syntax Def      ::= "%fdecl" "(" Decorators "," Id "," Params "," Type "," Stmts ")"
#    syntax Defs     ::= List{Def, ""}
#
# ex:
#  %fdecl(%@public %@payable, deposit, ,%void,
#    %assign(%var(_value), %as_num256(%msg.value))
#    %assign(%var(_sender), %msg.sender)
#    %assign(%mapelem(%svar(balances), %var(_sender)), %num256_add(%mapelem(%svar(balances), %var(_sender)), %var(_value)))
#    %assign(%svar(num_issued), %num256_add(%svar(num_issued), %var(_value)))
#    %log(Transfer, %hex("0000000000000000000000000000000000000000"), %var(_sender), %var(_value)))
def parseDef(node):
    return "  %fdecl(" + parseDecorators(node.decorator_list) + ", " + node.name + ", " + parseParams() + ", " \
           + parseType(node.returns) + "," + parseStmts(node.body) + ")"


# Pgm ::= "%pgm" "(" Events "," Globals "," Defs ")"
def parseProgram(nodeList):
    rez = "%pgm("
    events = []
    globals = []
    defs = []
    for node in nodeList:
        if type(node) == ast.AnnAssign and type(node.annotation) == ast.Call:
            events.append(parseEvent(node))
        elif type(node) == ast.AnnAssign:
            globals.append(parseGlobal(node))
        elif type(node) == ast.FunctionDef:
            defs.append(parseDef(node))
        else:
            raise ParserException("Unsupported top level node: " + str(node))
    for event in events:
        rez += "\n" + event
    rez += ","
    for globalN in globals:
        rez += "\n" + globalN
    rez += ","
    for defN in defs:
        rez += "\n" + defN
    rez += "\n)"
    return rez


def fullAstListToString(nodeList):
    rez = ""
    for node in nodeList:
        if rez != "":
            rez += ", "
        rez += fullAst(node)
    return rez


def fullAst(node):
    nodeType = type(node)

    # Python 3 AST. Source: https://docs.python.org/3/library/ast.html

    #    mod = Module(stmt* body)
    if nodeType == ast.Module:
        return "Module([" + fullAstListToString(node.body) + "])"

    # | Interactive(stmt* body)
    elif nodeType == ast.Interactive:
        return "Interactive([" + fullAstListToString(node.body) + "])"

    # | Expression(expr body)
    elif nodeType == ast.Expression:
        return "Expression([" + fullAst(node.body) + "])"

    # -- not really an actual node but useful in Jython's typesystem.
    #        | Suite(stmt* body)
    elif nodeType == ast.Suite:
        return "Suite([" + fullAstListToString(node.body) + "])"

    # stmt = FunctionDef(identifier name, arguments args, stmt* body, expr* decorator_list, expr? returns)
    elif nodeType == ast.FunctionDef:
        return "FunctionDef(" + node.name + ", args: [" + fullAstListToString(node.args) + "]" \
               + ", body: [" + fullAstListToString(node.body) + "]" \
               + ")"

    # | AsyncFunctionDef(identifier name, arguments args, stmt* body, expr* decorator_list, expr? returns)
    elif nodeType == ast.AsyncFunctionDef:
        raise ParserException("Unsupported AST node type: " + node)

    # | ClassDef(identifier name, expr* bases, keyword* keywords, stmt* body, expr* decorator_list)
    elif nodeType == ast.ClassDef:
        return "ClassDef(" + node.name + ", bases: [" + fullAstListToString(node.bases) + "]" \
               + ", body: [" + fullAstListToString(node.body) + "]" \
               + ")"

    # | Return(expr? value)
    elif nodeType == ast.Return:
        return "Return(" + fullAst(node.value) + ")"  # todo case no return value

    # | Delete(expr* targets)
    elif nodeType == ast.Delete:
        return "Delete([" + fullAstListToString(node.targets) + "])"

    # | Assign(expr* targets, expr value)
    elif nodeType == ast.Assign:
        return "Assign([" + fullAstListToString(node.targets) + "] = " + fullAst(node.value) + ")"

    # | AugAssign(expr target, operator op, expr value)
    elif nodeType == ast.AugAssign:
        return "AugAssign(" + fullAst(node.target) + ", " + fullAst(node.op) + ", " + fullAst(node.value) + ")"

    # todo stopped here
    #          -- 'simple' indicates that we annotate simple name without parens
    #          | AnnAssign(expr target, expr annotation, expr? value, int simple)
    elif nodeType == ast.AnnAssign:
        raise ParserException("Unsupported AST node type: " + node)

    # -- use 'orelse' because else is a keyword in target languages
    #          | For(expr target, expr iter, stmt* body, stmt* orelse)
    elif nodeType == ast.For:
        raise ParserException("Unsupported AST node type: " + node)

    # | AsyncFor(expr target, expr iter, stmt* body, stmt* orelse)
    elif nodeType == ast.AsyncFor:
        raise ParserException("Unsupported AST node type: " + node)

    # | While(expr test, stmt* body, stmt* orelse)
    elif nodeType == ast.While:
        raise ParserException("Unsupported AST node type: " + node)

    # | If(expr test, stmt* body, stmt* orelse)
    elif nodeType == ast.If:
        raise ParserException("Unsupported AST node type: " + node)

    # | With(withitem* items, stmt* body)
    elif nodeType == ast.With:
        raise ParserException("Unsupported AST node type: " + node)

    # | AsyncWith(withitem* items, stmt* body)
    elif nodeType == ast.AsyncWith:
        raise ParserException("Unsupported AST node type: " + node)

    # | Raise(expr? exc, expr? cause)
    elif nodeType == ast.Raise:
        raise ParserException("Unsupported AST node type: " + node)

    # | Try(stmt* body, excepthandler* handlers, stmt* orelse, stmt* finalbody)
    elif nodeType == ast.Try:
        raise ParserException("Unsupported AST node type: " + node)

    # | Assert(expr test, expr? msg)
    elif nodeType == ast.Assert:
        raise ParserException("Unsupported AST node type: " + node)

    # | Import(alias* names)
    elif nodeType == ast.Import:
        raise ParserException("Unsupported AST node type: " + node)

    # | ImportFrom(identifier? module, alias* names, int? level)
    elif nodeType == ast.ImportFrom:
        raise ParserException("Unsupported AST node type: " + node)

    # | Global(identifier* names)
    elif nodeType == ast.Global:
        raise ParserException("Unsupported AST node type: " + node)

    # | Nonlocal(identifier* names)
    elif nodeType == ast.Nonlocal:
        raise ParserException("Unsupported AST node type: " + node)

    # | Expr(expr value)
    elif nodeType == ast.Expr:
        raise ParserException("Unsupported AST node type: " + node)

    # | Pass | Break | Continue
    elif nodeType == ast.Pass or nodeType == ast.Break or nodeType == ast.Continue:
        raise ParserException("Unsupported AST node type: " + node)


    # -- BoolOp() can use left & right?
    #    expr = BoolOp(boolop op, expr* values)
    elif nodeType == ast.BoolOp:
        raise ParserException("Unsupported AST node type: " + node)

    # | BinOp(expr left, operator op, expr right)
    elif nodeType == ast.BinOp:
        raise ParserException("Unsupported AST node type: " + node)

    # | UnaryOp(unaryop op, expr operand)
    elif nodeType == ast.UnaryOp:
        raise ParserException("Unsupported AST node type: " + node)

    # | Lambda(arguments args, expr body)
    elif nodeType == ast.Lambda:
        raise ParserException("Unsupported AST node type: " + node)

    # | IfExp(expr test, expr body, expr orelse)
    elif nodeType == ast.IfExp:
        raise ParserException("Unsupported AST node type: " + node)

    # | Dict(expr* keys, expr* values)
    elif nodeType == ast.Dict:
        raise ParserException("Unsupported AST node type: " + node)

    # | Set(expr* elts)
    elif nodeType == ast.Set:
        raise ParserException("Unsupported AST node type: " + node)

    # | ListComp(expr elt, comprehension* generators)
    elif nodeType == ast.ListComp:
        raise ParserException("Unsupported AST node type: " + node)

    # | SetComp(expr elt, comprehension* generators)
    elif nodeType == ast.SetComp:
        raise ParserException("Unsupported AST node type: " + node)

    # | DictComp(expr key, expr value, comprehension* generators)
    elif nodeType == ast.DictComp:
        raise ParserException("Unsupported AST node type: " + node)

    # | GeneratorExp(expr elt, comprehension* generators)
    elif nodeType == ast.GeneratorExp:
        raise ParserException("Unsupported AST node type: " + node)

    # -- the grammar constrains where yield expressions can occur
    #         | Await(expr value)
    elif nodeType == ast.Await:
        raise ParserException("Unsupported AST node type: " + node)

    # | Yield(expr? value)
    elif nodeType == ast.Yield:
        raise ParserException("Unsupported AST node type: " + node)

    # | YieldFrom(expr value)
    elif nodeType == ast.YieldFrom:
        raise ParserException("Unsupported AST node type: " + node)

    # -- need sequences for compare to distinguish between
    #         -- x < 4 < 3 and (x < 4) < 3
    #         | Compare(expr left, cmpop* ops, expr* comparators)
    elif nodeType == ast.Compare:
        raise ParserException("Unsupported AST node type: " + node)

    # | Call(expr func, expr* args, keyword* keywords)
    elif nodeType == ast.Call:
        raise ParserException("Unsupported AST node type: " + node)

    # | Num(object n) -- a number as a PyObject.
    elif nodeType == ast.Num:
        raise ParserException("Unsupported AST node type: " + node)

    # | Str(string s) -- need to specify raw, unicode, etc?
    elif nodeType == ast.Str:
        raise ParserException("Unsupported AST node type: " + node)

    # | FormattedValue(expr value, int? conversion, expr? format_spec)
    elif nodeType == ast.FormattedValue:
        raise ParserException("Unsupported AST node type: " + node)

    # | JoinedStr(expr* values)
    elif nodeType == ast.JoinedStr:
        raise ParserException("Unsupported AST node type: " + node)

    # | Bytes(bytes s)
    elif nodeType == ast.Bytes:
        raise ParserException("Unsupported AST node type: " + node)

    # | NameConstant(singleton value)
    elif nodeType == ast.NameConstant:
        raise ParserException("Unsupported AST node type: " + node)

    # | Ellipsis
    elif nodeType == ast.Ellipsis:
        raise ParserException("Unsupported AST node type: " + node)

    # | Constant(constant value)
    elif nodeType == ast.Constant:
        raise ParserException("Unsupported AST node type: " + node)

    # -- the following expression can appear in assignment context
    #         | Attribute(expr value, identifier attr, expr_context ctx)
    elif nodeType == ast.Attribute:
        raise ParserException("Unsupported AST node type: " + node)

    # | Subscript(expr value, slice slice, expr_context ctx)
    elif nodeType == ast.Subscript:
        raise ParserException("Unsupported AST node type: " + node)

    # | Starred(expr value, expr_context ctx)
    elif nodeType == ast.Starred:
        raise ParserException("Unsupported AST node type: " + node)

    # | Name(identifier id, expr_context ctx)
    elif nodeType == ast.Name:
        raise ParserException("Unsupported AST node type: " + node)

    # | List(expr* elts, expr_context ctx)
    elif nodeType == ast.List:
        raise ParserException("Unsupported AST node type: " + node)

    # | Tuple(expr* elts, expr_context ctx)
    elif nodeType == ast.Tuple:
        raise ParserException("Unsupported AST node type: " + node)


    # expr_context = Load | Store | Del | AugLoad | AugStore | Param
    elif nodeType == ast.Load or nodeType == ast.Store or nodeType == ast.Del or nodeType == ast.AugLoad \
            or nodeType == ast.AugStore or nodeType == ast.Param:
        raise ParserException("Unsupported AST node type: " + node)

    # slice = Slice(expr? lower, expr? upper, expr? step)
    elif nodeType == ast.Slice:
        raise ParserException("Unsupported AST node type: " + node)

    # | ExtSlice(slice* dims)
    elif nodeType == ast.ExtSlice:
        raise ParserException("Unsupported AST node type: " + node)

    # | Index(expr value)
    elif nodeType == ast.Index:
        raise ParserException("Unsupported AST node type: " + node)

    # boolop = And | Or
    elif nodeType == nodeType == ast.And or nodeType == ast.Or:
        raise ParserException("Unsupported AST node type: " + node)

    # operator = Add | Sub | Mult | MatMult | Div | Mod | Pow | LShift
    #                 | RShift | BitOr | BitXor | BitAnd | FloorDiv
    elif nodeType == ast.Add or nodeType == ast.Sub or nodeType == ast.Mult or nodeType == ast.MatMult \
            or nodeType == ast.Div or nodeType == ast.Mod or nodeType == ast.Pow or nodeType == ast.LShift \
            or nodeType == ast.RShift or nodeType == ast.BitOr or nodeType == ast.BitXor or nodeType == ast.BitAnd \
            or nodeType == ast.FloorDiv:
        raise ParserException("Unsupported AST node type: " + node)

    # unaryop = Invert | Not | UAdd | USub
    elif nodeType == ast.Invert or nodeType == ast.Not or nodeType == ast.UAdd or nodeType == ast.USub:
        raise ParserException("Unsupported AST node type: " + node)

    # cmpop = Eq | NotEq | Lt | LtE | Gt | GtE | Is | IsNot | In | NotIn
    elif nodeType == ast.Eq or nodeType == ast.NotEq or nodeType == ast.Lt or nodeType == ast.LtE \
            or nodeType == ast.Gt or nodeType == ast.GtE or nodeType == ast.Is or nodeType == ast.IsNot \
            or nodeType == ast.In or nodeType == ast.NotIn:
        raise ParserException("Unsupported AST node type: " + node)

    # comprehension = (expr target, expr iter, expr* ifs, int is_async)
    elif nodeType == ast.comprehension:
        raise ParserException("Unsupported AST node type: " + node)

    # excepthandler = ExceptHandler(expr? type, identifier? name, stmt* body)
    #                    attributes (int lineno, int col_offset)
    elif nodeType == ast.ExceptHandler:
        raise ParserException("Unsupported AST node type: " + node)

    # arguments = (arg* args, arg? vararg, arg* kwonlyargs, expr* kw_defaults,
    #                 arg? kwarg, expr* defaults)
    elif nodeType == ast.arguments:
        raise ParserException("Unsupported AST node type: " + node)

    # arg = (identifier arg, expr? annotation)
    #           attributes (int lineno, int col_offset)
    elif nodeType == ast.arg:
        raise ParserException("Unsupported AST node type: " + node)

    # -- keyword arguments supplied to call (NULL identifier for **kwargs)
    #    keyword = (identifier? arg, expr value)
    elif nodeType == ast.keyword:
        raise ParserException("Unsupported AST node type: " + node)

    # -- import name with optional 'as' alias.
    #    alias = (identifier name, identifier? asname)
    elif nodeType == ast.alias:
        raise ParserException("Unsupported AST node type: " + node)

    # withitem = (expr context_expr, expr? optional_vars)
    elif nodeType == ast.withitem:
        raise ParserException("Unsupported AST node type: " + node)

    else:
        raise ParserException("Node type not defined in Python 3: " + node)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("One argument expected: the file name.")
        sys.exit(1)
    fileName = sys.argv[1]
    with open(fileName, "r") as fin:
        input = fin.read()
    astList = parse(input)
    print(parseProgram(astList))
