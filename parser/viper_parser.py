#!/usr/bin/env python3.6

import sys
import ast
import types

from typing import List


class ParserException(Exception):
    pass


def get_original_if_0x_prefixed(expr):
    context_slice = inputLines[expr.lineno - 1][expr.col_offset:]
    if context_slice[:2] != '0x':
        return None
    t = 0
    while t + 2 < len(context_slice) and context_slice[t + 2] in '0123456789abcdefABCDEF':
        t += 1
    return context_slice[:t + 2]


def resolve_negative_literals(_ast):
    class RewriteUnaryOp(ast.NodeTransformer):
        def visit_UnaryOp(self, node):
            if isinstance(node.op, ast.USub) and isinstance(node.operand, ast.Num):
                node.operand.n = 0 - node.operand.n
                return node.operand
            else:
                return node

    return RewriteUnaryOp().visit(_ast)


def parse(code):
    o = ast.parse(code)
    o = resolve_negative_literals(o)
    return o.body


def parseList(nodeList, parseElement: types.FunctionType, separator, initSeparator="", emptyCase=""):
    rez = ""
    first = True
    for node in nodeList:
        if first:
            first = False
            rez += initSeparator
        else:
            rez += separator
        rez += parseElement(node)
    return rez if rez != "" else emptyCase


# syntax BaseType      ::= "%bool"
#                         | NumericType | "%num256"  | "%signed256"
#                         | "%bytes32" | "%address"
# syntax NumericType   ::= PureNumType
#                        | UnitType
# syntax PureNumType   ::= "%num" | "%decimal"
def parseBaseType(name):  # value is Str. NumericType not yet supported
    if type(name) == ast.Name:
        return "%" + name.id
    else:
        raise ParserException("BaseType parsing not yet implemented for: " + str(id))


# syntax Unit          ::= BaseUnit
#                        | "%umul" "(" Unit "," Unit ")"
#                        | "%udiv" "(" Unit "," Unit ")"
#                        | "%upow" "(" BaseUnit "," Int ")"
#
# syntax BaseUnit      ::= "%wei" | "%currency" | "%currency1" | "%currency2"
#                        | "%sec" | "%m"        | "%kg"
#
# wei / sec =>
#   %udiv(%wei, %sec)
def parseUnit(node):
    unitOpMap = {
        ast.Mult: "%umul",
        ast.Div: "%udiv",
        ast.Pow: "%upow"
    }
    if type(node) == ast.Name:  # base unit
        return "%{}".format(node.id)
    elif type(node) == ast.Num:  # to support 2nd argument of %upow
        return node.n
    elif type(node) == ast.BinOp:
        return "{}({}, {})".format(unitOpMap[type(node.op)], parseUnit(node.left), parseUnit(node.right))
    else:
        raise ParserException("Unsupported Unit format: " + str(node))


# syntax UnitType      ::= "%unitT" "(" PureNumType "," Unit "," Bool /*positional*/ ")"
#
# num(wei / sec)
#   => %unitT(%num, %udiv(%wei, %sec), false)
def parseUnitType(node: ast.Call):
    return "%unitT({}, {}, false)".format(parseType(node.func), parseUnit(node.args[0]))


# syntax StructType    ::= "%structT" "(" VarDecls ")"
#
# Example: {f1:num, f2:num}
def parseStructType(node: ast.Dict):
    return "%structT({})".format(parseVarDecls(node))


# syntax Type          ::= "%void"
#                           | BaseType
#                           | ByteArrayType
#                           | ListType
#                           | MappingType
#                           | StructType
#
# syntax ListType      ::= "%listT"   "(" Type "," Int ")"
#
# syntax MappingType   ::= "%mapT"    "(" Type "," BaseType ")"
#
# example:
#   %mapT(%num256, %address)
def parseType(param):
    if param is None:
        return "%void"
    elif type(param) == ast.Name:
        return parseBaseType(param)
    elif type(param) == ast.Subscript:
        if type(param.slice.value) == ast.Num:
            return "%listT({}, {})".format(parseType(param.value), parseConst(param.slice.value))
        else:
            return "%mapT({}, {})".format(parseType(param.value), parseType(param.slice.value))
    elif type(param) == ast.Call:
        return parseUnitType(param)
    elif type(param) == ast.Dict:
        return parseStructType(param)
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


def parseEventParams(node: ast.Dict):
    rez = ""
    for i in range(0, len(node.keys)):
        key = node.keys[i]
        value = node.values[i]
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
#
# x: public(num(wei / sec))
#   => %svdecl(x, %unitT(%num, %udiv(%wei, %sec), false), %public)
def parseGlobal(node):
    if type(node.annotation) == ast.Call:
        return "  %svdecl({}, {}, %{})" \
            .format(node.target.id, parseType(node.annotation.args[0]), node.annotation.func.id)
    else:
        return "  %svdecl({}, {}, %private)".format(node.target.id, parseType(node.annotation))


#    syntax Decorator  ::= "%@constant" | "%@payable" | "%@internal" | "%@public"
#    syntax Decorators ::= List{Decorator, ""}
def parseDecorator(name):
    return "%@" + name.id


def parseDecorators(decorator_list):
    return parseList(decorator_list, parseDecorator, " ")


# syntax Param    ::= "%param" "(" Id "," Type ")"
#
# example: %param(_value, %num256)
def parseParam(arg: ast.arg):
    return "%param({}, {})".format(arg.arg, parseType(arg.annotation))


# syntax Params   ::= List{Param, ""}
def parseParams(args: List[ast.arg]):
    return parseList(args, parseParam, " ")


# syntax Var      ::= "%var"  "(" Id ")"
#                   | "%svar" "(" Id ")"
#                   | StructFieldVar
#                   | SubscriptVar
#
# syntax StructFieldVar  ::= "%field"     "(" Var "," Id   ")"  // struct field access
#
# syntax SubscriptVar    ::= "%subscript" "(" Var "," Expr ")"  // list or map element
#
# examples:
#   %var(_value)
#   %svar(balances)
#   self.balances[_sender]  =>  %subscript(%svar(balances), %var(_sender))
#   %subscript(%var(x), 0)
def parseVar(var):
    if type(var) == ast.Name:
        return "%var(" + var.id + ")"
    elif type(var) == ast.Index:  # same as ast.Name
        return parseVar(var.value)
    elif type(var) == ast.Attribute:
        if type(var.value) == ast.Name and var.value.id == "self":
            return "%svar({})".format(var.attr)
        else:
            return "%field({}, {})".format(parseVar(var.value), var.attr)
    elif type(var) == ast.Subscript:
        return "%subscript({}, {})".format(parseVar(var.value), parseExpr(var.slice))
    else:
        raise ParserException("Unsupported Var format: " + str(var))


# taken from viper compiler.
DECIMAL_DIVISOR = 10000000000


def parseFixed10Const(node):
    # num = Decimal(node.n) - leads to weird digits many places after "." in simple numbers like 2.1
    num = node.n
    divisor = 1
    while num % 1 != 0 and divisor < DECIMAL_DIVISOR:
        num *= 10
        divisor *= 10
    return "%fixed10({0:.0f}, {1})".format(num, divisor)


# syntax Const    ::= Int
#                   | "%hex"     "(" String ")"
#                   | "%fixed10" "(" Int "," Int ")"  // decimal fixed point value with a precision of 10 decimal places
#                                                     // %fixed10(A, B) = A/B and B is a power of 10.
#                   | String
#                   | Bool
#
def parseConst(node):
    boolMap = {True: "true", False: "false"}
    if type(node) == ast.Num and type(node.n) == int:
        hexFormat = get_original_if_0x_prefixed(node)
        if hexFormat is None:
            return str(node.n)
        else:
            return "%hex(\"{}\")".format(hexFormat[2:])
    elif type(node) == ast.Num and type(node.n == float):
        return parseFixed10Const(node)
    elif type(node) == ast.Str:
        return "\"{}\"".format(node.s)
    elif type(node) == ast.NameConstant:
        return boolMap[node.value]
    elif type(node) == ast.Name and node.id in ["true", "false"]:
        return node.id
    else:
        raise ParserException("Unsupported Const format: " + str(node))


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
#   %num256_add(%subscript(%svar(balances), %var(_sender)), %var(_value))
#
#   %as_wei_value(%as_num128(%var(_value)), wei)
def parseCallExpr(expr: ast.Call):
    if len(expr.keywords) != 0:
        raise ParserException("Calls with named parameters not yet supported: " + str(expr.keywords))
    if expr.func.id == "as_wei_value":
        return "%as_wei_value({}, {})".format(parseExpr(expr.args[0]), expr.args[1].id)
    else:
        return "%{}({})".format(expr.func.id, parseExprs(expr.args, ", "))


# syntax ReservedExpr  ::= "%msg.sender" | "%msg.value" | "%msg.gas"
#                        | "%block.difficulty" | "%block.timestamp" | "%block.coinbase" | "%block.number"
#                        | "%block.prevhash"
#                        | "%tx.origin"
#
# If no reserved expression found, returns None.
def tryParseReservedExpr(expr):
    optionsMap = {"msg": ["sender", "value", "gas"],
                  "block": ["difficulty", "timestamp", "coinbase", "number", "prevhash"],
                  "tx": ["origin"]}
    values = optionsMap.get(expr.value.id)
    if values is not None and expr.attr in values:
        return "%" + expr.value.id + "." + expr.attr
    return None


# syntax CompareOp     ::= "%lt" | "%le" | "%gt" | "%ge" | "%eq" | "%ne" | "%in"
def parseCompareOp(op: ast.cmpop):
    map = {ast.Eq: "%eq",
           ast.Gt: "%gt",
           ast.GtE: "%ge",
           ast.In: "%in",
           ast.Is: None,
           ast.IsNot: None,
           ast.Lt: "%lt",
           ast.LtE: "%le",
           ast.NotEq: "%ne",
           ast.NotIn: None
           }
    if map[type(op)] is not None:
        return map[type(op)]
    else:
        raise ParserException("Unsupported CompareOp: " + str(op) + " in " + inputLines[op.lineno][op.col_offset:])


# syntax Expr     ::= Const
#                   | Var
#                   | ListExpr
#                   | "%self"
#                   | "%binop"     "(" BinOp     "," Expr "," Expr ")"
#                   | "%compareop" "(" CompareOp "," Expr "," Expr ")"
#                   | "%boolop"    "(" BoolOp    "," Expr "," Expr ")"
#                   | "%unaryop"   "(" UnaryOp   "," Expr ")"
#                   | "%icall"     "(" Id        "," Exprs ")"  // internal contract call
#                   | "%ecall"     "(" Id        "," Exprs ")"  // external contract call
#                   | ReservedExpr
#                   | ReservedFunc  // expr dispatch table
#
# syntax ListExpr      ::= "%list" "(" Exprs ")"
#
# examples:
#   %var(_sender)
#   %as_num256(%msg.value)
#   %msg.value
#   %subscript(%svar(balances), %var(_sender))
#   %binop(+, %var(x), 10)
def parseExpr(expr):
    if type(expr) == ast.Index:
        return parseExpr(expr.value)
    elif type(expr) == ast.Num or type(expr) == ast.Str or type(expr) == ast.NameConstant \
            or (type(expr) == ast.Name and expr.id in ["true", "false"]):
        return parseConst(expr)
    elif type(expr) == ast.Name and expr.id == "self":
        return "%self"
    elif type(expr) == ast.BinOp:
        return "%binop({}, {}, {})".format(parseBinOp(expr.op), parseExpr(expr.left), parseExpr(expr.right))
    elif type(expr) == ast.Compare:
        if len(expr.ops) > 1 or len(expr.comparators) > 1:
            raise ParserException("Unsupported complex comparator format: " + inputLines[expr.lineno][expr.col_offset:])
        return "%compareop({}, {}, {})" \
            .format(parseCompareOp(expr.ops[0]), parseExpr(expr.left), parseExpr(expr.comparators[0]))
    elif type(expr) == ast.Attribute and type(expr.value) == ast.Name:
        rez = tryParseReservedExpr(expr)
        if rez is not None:
            return rez
        else:
            return parseVar(expr)
    elif type(expr) == ast.Name or type(expr) == ast.Subscript or type(expr) == ast.Attribute:
        return parseVar(expr)
    elif type(expr) == ast.List:
        return "%list({})".format(parseExprs(expr.elts))
    elif type(expr) == ast.Call and type(expr.func) == ast.Name:
        return parseCallExpr(expr)
    elif type(expr) == ast.Call and type(expr.func) == ast.Attribute and expr.func.value.id == "self":
        return "%icall({}, {})".format(expr.func.attr, parseExprs(expr.args))
    else:
        raise ParserException("Unsupported Expr format: " + str(expr))


# syntax Exprs    ::= List{Expr, ""}
def parseExprs(exprs, separator=" "):
    return parseList(exprs, parseExpr, separator)


# syntax BinOp         ::= "+" | "-" | "*" | "/" | "%" | "**"
#
# we'll support all operators from Python.
def parseBinOp(op: ast.operator):
    opType = type(op)
    if opType == ast.Add:
        return "+"
    elif opType == ast.BitAnd:
        return "&"
    elif opType == ast.BitOr:
        return "|"
    elif opType == ast.BitXor:
        return "^"
    elif opType == ast.Div:
        return "/"
    elif opType == ast.FloorDiv:
        return "//"
    elif opType == ast.LShift:
        return "<<"
    elif opType == ast.MatMult:
        return "@"
    elif opType == ast.Mod:
        return "%"
    elif opType == ast.Mult:
        return "*"
    elif opType == ast.Pow:
        return "**"
    elif opType == ast.RShift:
        return ">>"
    elif opType == ast.Sub:
        return "-"
    else:
        raise ParserException("Unsupported AugAssign operator: " + str(op))


# syntax AugAssignOp ::= "+=" | "-=" | "*=" | "/=" | "%="
def parseAugAssignOp(op: ast.operator):
    return "{}=".format(parseBinOp(op))


# syntax VarDecl  ::= "%vdecl" "(" Id "," Type ")"
#
# ex: %vdecl(a, %listT(%num, 5))
def parseVarDecl(stmt: ast.AnnAssign):
    return parseVarDecl2(stmt.target, stmt.annotation)


def parseVarDecl2(key, value):
    return "%vdecl({}, {})".format(key.id, parseType(value))


# syntax VarDecls ::= List{VarDecl, ""}
def parseVarDecls(dict: ast.Dict):
    rez = ""
    for i in range(0, len(dict.keys)):
        key = dict.keys[i]
        value = dict.values[i]
        if rez != "":
            rez += " "
        rez += parseVarDecl2(key, value)
    return rez


# syntax Stmt     ::= VarDecl                                              // annotated assign
#                   | "%assign"    "(" Var "," Expr ")"
#                   | "%augassign" "(" AugAssignOp "," Var "," Expr ")"
#                   | "%if"        "(" Expr "," Stmts "," Stmts ")"
#                   | "%if"        "(" Expr "," Stmts ")"
#                   | "%forrange"  "(" Id "," Int  "," Stmts ")"            // for i in range(rounds)
#                   | "%forrange"  "(" Id "," Expr "," Expr  "," Stmts ")"  // for i in range(start, start + rounds)
#                   | "%forlist"   "(" Id "," Expr "," Stmts ")"            // for i in list()
#                   | "%break"
#                   | "%pass"
#                   | "%return"
#                   | "%return"    "(" Expr ")"
#                   | "%assert"    "(" Expr ")"
#                   | "%throw"
#                   | "%log"       "(" Id "," Exprs ")"
#                   // stmt dispatch table
#                   | "%send"      "(" Expr  "," Expr ")"
#                   | "%selfdestruct" "(" Expr ")"
#
# examples:
#   _value = as_num256(msg.value)
#   =>
#   %assign(%var(_value), %as_num256(%msg.value))
#
#   log.Transfer(0x0000000000000000000000000000000000000000, _sender, _value)
#   =>
#   %log(Transfer, %hex("0000000000000000000000000000000000000000"), %var(_sender), %var(_value)))
#
#   send(_sender, as_wei_value(as_num128(_value), wei))
#   =>
#   %send(%var(_sender), %as_wei_value(%as_num128(%var(_value)), wei))
#
# %augassign(+=, %var(z), %var(y))
#
#  %if(%var(i),
#    %return(5),
#    %return(7))
#
# %forrange(i, 10, %pass)
def parseStmt(stmt):
    if type(stmt) == ast.AnnAssign:
        return parseVarDecl(stmt)
    elif type(stmt) == ast.Assign:
        return "%assign({}, {})".format(parseVar(stmt.targets[0]), parseExpr(stmt.value))
    elif type(stmt) == ast.AugAssign:
        return "%augassign({}, {}, {})".format(parseAugAssignOp(stmt.op), parseVar(stmt.target),
                                               parseExpr(stmt.value))
    elif type(stmt) == ast.Expr and type(stmt.value) == ast.Call:
        if type(stmt.value.func) == ast.Attribute and stmt.value.func.value.id == "log":
            return "%log({}, {})".format(stmt.value.func.attr, parseExprs(stmt.value.args))
        elif type(stmt.value.func) == ast.Name and stmt.value.func.id == "send":
            return "%send({})".format(parseExprs(stmt.value.args, ", "))
        elif type(stmt.value.func) == ast.Name and stmt.value.func.id == "selfdestruct":
            return "%selfdestruct({})".format(parseExprs(stmt.value.args, ", "))
        else:
            raise ParserException("Unsupported Expr Stmt format: " + str(stmt))
    elif type(stmt) == ast.If:
        if len(stmt.orelse) == 0:
            return "%if({},{})".format(parseExpr(stmt.test), parseStmts(stmt.body))
        else:
            return "%if({},{},{})".format(parseExpr(stmt.test), parseStmts(stmt.body), parseStmts(stmt.orelse))
    elif type(stmt) == ast.For and stmt.iter.func.id == "range":
        if len(stmt.iter.args) == 1:
            return "%forrange({}, {},{})".format(stmt.target.id, parseExpr(stmt.iter.args[0]), parseStmts(stmt.body))
        else:
            return "%forrange({}, {}, {},{})".format(stmt.target.id, parseExpr(stmt.iter.args[0]),
                                                     parseExpr(stmt.iter.args[1]), parseStmts(stmt.body))
    elif type(stmt) == ast.Pass:
        return "%pass"
    elif type(stmt) == ast.Return:
        if stmt.value is None:
            return "%return"
        else:
            return "%return({})".format(parseExpr(stmt.value))
    elif type(stmt) == ast.Assert:
        return "%assert({})".format(parseExpr(stmt.test))
    else:
        raise ParserException("Unsupported Stmt format: " + str(stmt))


stmtsIndent = "  "


# syntax Stmts    ::= List{Stmt, ""}
def parseStmts(body):
    global stmtsIndent
    oldStmtsIndent = stmtsIndent
    stmtsIndent += "  "
    rez = parseList(body, parseStmt, "\n" + stmtsIndent, "\n" + stmtsIndent)
    stmtsIndent = oldStmtsIndent
    return rez


#    syntax Def      ::= "%fdecl" "(" Decorators "," Id "," Params "," Type "," Stmts ")"
#    syntax Defs     ::= List{Def, ""}
#
# ex:
#  %fdecl(%@public %@payable, deposit, ,%void,
#    %assign(%var(_value), %as_num256(%msg.value))
#    ...)
def parseDef(node):
    return "  %fdecl({}, {}, {}, {},{})".format(
        parseDecorators(node.decorator_list),
        node.name,
        parseParams(node.args.args),
        parseType(node.returns),
        parseStmts(node.body)
    )


# Pgm ::= "%pgm" "(" Events "," Globals "," Defs ")"
def parseProgram(nodeList):
    events = []
    globals = []
    defs = []
    for node in nodeList:
        if type(node) == ast.AnnAssign and type(node.annotation) == ast.Call and node.annotation.func.id == "__log__":
            events.append(node)
        elif type(node) == ast.AnnAssign:
            globals.append(node)
        elif type(node) == ast.FunctionDef:
            defs.append(node)
        else:
            raise ParserException("Unsupported top level node: " + str(node))
    return "%pgm({},{},{}\n)".format(
        parseList(events, parseEvent, "\n", "\n"),
        parseList(globals, parseGlobal, "\n", "\n", " "),
        parseList(defs, parseDef, "\n", "\n", " "))


inputLines: List[str]

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("One argument expected: the file name.")
        sys.exit(1)
    fileName = sys.argv[1]
    with open(fileName, "r") as fin:
        input = fin.read()
    inputLines = input.splitlines()
    astList = parse(input)
    print(parseProgram(astList))
