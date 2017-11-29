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


def parse(code):
    o = ast.parse(code)
    # todo fix those
    # decorate_ast_with_source(o, code)
    # o = resolve_negative_literals(o)
    return o.body


def parseList(nodeList, parseElement: types.FunctionType, separator):
    rez = ""
    first = True
    for node in nodeList:
        if first:
            first = False
        else:
            rez += separator
        rez += parseElement(node)
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
    return parseList(decorator_list, parseDecorator, " ")


# syntax Param    ::= "%param" "(" Id "," Type ")"
#
# example: %param(_value, %num256)
def parseParam(arg: ast.arg):
    return "%param({}, {})".format(arg.arg, parseType(arg.annotation))


# syntax Params   ::= List{Param, ""}
def parseParams(args: List[ast.arg]):
    return parseList(args, parseParam, " ")


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


# syntax Const    ::= Int
#                   | "%hex"     "(" String ")"
#                   | "%fixed10" "(" Int "," Int ")"  // decimal fixed point value with a precision of 10 decimal places
#                                                     // %fixed10(A, B) = A/B and B is a power of 10.
#                   | String
#                   | Bool
#
# note: hex is not possible because Python converts it to regular int.
def parseConst(node):
    if type(node) == ast.Num:
        hexFormat = get_original_if_0x_prefixed(node)
        if hexFormat is None:
            return str(node.n)
        else:
            return "%hex(\"{}\")".format(hexFormat[2:])
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
#   %num256_add(%mapelem(%svar(balances), %var(_sender)), %var(_value))
#
#   %as_wei_value(%as_num128(%var(_value)), wei)
def parseCallExpr(expr):
    if expr.func.id == "as_wei_value":
        return "%as_wei_value({}, {})".format(parseExpr(expr.args[0]), expr.args[1].id)
    else:
        return "%{}({})".format(expr.func.id, parseExprs(expr.args, ", "))


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
    if type(expr) == ast.Num or (type(expr) == ast.Name and expr.id in ["true", "false"]):
        return parseConst(expr)
    elif type(expr) == ast.Name or type(expr) == ast.Index or type(expr) == ast.Subscript \
            or (type(expr) == ast.Attribute and expr.value.id == "self"):
        return parseVar(expr)
    elif type(expr) == ast.Attribute:
        return parseReservedExpr(expr)
    elif type(expr) == ast.Call:
        return parseCallExpr(expr)
    else:
        raise ParserException("Unsupported Expr format: " + str(expr))


# syntax Exprs    ::= List{Expr, ""}
def parseExprs(exprs, separator=" "):
    return parseList(exprs, parseExpr, separator)


# syntax Stmt     ::= VarDecl  // annotated assign
#                  | "%assign"    "(" Var "," Expr ")"
#                  | "%augassign" "(" AugAssignOp "," Var "," Expr ")"
#                  | "%if"        "(" Expr "," Stmts "," Stmts ")"
#                  | "%if"        "(" Expr "," Stmts ")"
#                  | "%for"       "(" Id "," Int "," Stmts ")"
#                  | "%for"       "(" Id "," Expr "," Expr "," Stmts ")"
#                  | "%break"
#                  | "%pass"
#                  | "%return"
#                  | "%return"    "(" Expr ")"
#                  | "%assert"    "(" Expr ")"
#                  | "%throw"
#                  | "%log"       "(" Id "," Exprs ")"
#                  // stmt dispatch table
#                  | "%send"      "(" Expr  "," Expr ")"
#                  | "%selfdestruct" "(" Expr ")"
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
def parseStmt(stmt):
    if type(stmt) == ast.Assign:
        return "\n    %assign({}, {})".format(parseVar(stmt.targets[0]), parseExpr(stmt.value))
    elif type(stmt) == ast.Expr and type(stmt.value) == ast.Call:
        if type(stmt.value.func) == ast.Attribute and stmt.value.func.value.id == "log":
            return "\n    %log({}, {})".format(stmt.value.func.attr, parseExprs(stmt.value.args))
        elif type(stmt.value.func) == ast.Name and stmt.value.func.id == "send":
            return "\n    %send({})".format(parseExprs(stmt.value.args, ", "))
        else:
            return "\n    "  # todo temp to see results
    elif type(stmt) == ast.Return:
        if stmt.value is None:
            return "\n    %return"
        else:
            return "\n    %return({})".format(parseExpr(stmt.value))
    else:
        return "\n    "  # todo temp to see results
        # raise ParserException("Unsupported Stmt format: " + str(stmt))


# syntax Stmts    ::= List{Stmt, ""}
def parseStmts(body):
    return parseList(body, parseStmt, "")


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
