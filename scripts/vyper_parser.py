#!/usr/bin/env python3.6

import sys
import ast
import types
import os

from typing import List


class ParserException(Exception):
    pass


class KVStructureException(Exception):
    pass


class KVTypeMismatchException(Exception):
    pass


def get_original_if_0x_prefixed(expr):
    context_slice = get_original_str_to_line_end(expr)
    if context_slice[:2] != '0x':
        return None
    t = 0
    while t + 2 < len(context_slice) and context_slice[t + 2] in '0123456789abcdefABCDEF':
        t += 1
    return context_slice[:t + 2]


def get_original_str(node: ast.Str):
    context_slice = get_original_str_to_line_end(node)
    t = 1
    # searching the closing "
    while t < len(context_slice) and context_slice[t:t + 1] != "\"":
        t += 1
    return context_slice[:t + 1]


def get_original_str_to_line_end(node: ast.AST):
    return inputLines[node.lineno - 1][node.col_offset:]


def get_number_as_fraction(expr):
    context_slice = get_original_str_to_line_end(expr)
    t = 0
    while t < len(context_slice) and context_slice[t] in '0123456789.':
        t += 1
    top = int(context_slice[:t].replace('.', ''))
    bottom = 1 if '.' not in context_slice[:t] else 10 ** (t - context_slice[:t].index('.') - 1)

    if expr.n < 0:
        top *= -1

    return top, bottom


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


def parseList(nodeList, parseElement: types.FunctionType, separator, initSeparator="", emptyCase="",
              doubleIndent=False):
    rez = ""
    first = True
    for node in nodeList:
        if first:
            first = False
            rez += initSeparator
        else:
            rez += separator
        rez += parseElement(node, doubleIndent) if doubleIndent else parseElement(node)
    return rez if rez != "" else emptyCase


def parseDict(nodeDict: ast.Dict, parseElement: types.FunctionType, separator, initSeparator="", emptyCase=""):
    rez = ""
    first = True
    for i in range(0, len(nodeDict.keys)):
        key = nodeDict.keys[i]
        value = nodeDict.values[i]
        if first:
            first = False
            rez += initSeparator
        else:
            rez += separator
        rez += parseElement(key, value)
    return rez if rez != "" else emptyCase


# syntax BaseType      ::= "%bool"
#                         | NumericType | "%num256"  | "%signed256"
#                         | "%bytes32" | "%address"
# syntax NumericType   ::= PureNumType
#                        | UnitType
# syntax PureNumType   ::= "%num" | "%decimal"
def parseBaseType(name: ast.Name):  # value is Str. NumericType not yet supported
    if type(name) == ast.Name:
        if name.id == "int128":
            return "%num"
        if name.id == "uint256":
            return "%num256"
        elif name.id in ["bool", "num256", "signed256", "bytes32", "address", "num", "decimal",
                         "timestamp", "timedelta", "currency_value", "currency1_value", "currency2_value", "wei_value",
                         "bytes"]:
            return "%{}".format(name.id)
        else:
            return "%contractT({})".format(name.id)
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


# syntax Type          ::= "%void"
#                           | BaseType
#                           | ByteArrayType
#                           | ListType
#                           | MappingType
#                           | StructType
#
# syntax ListType      ::= "%listT"   "(" Type "," Int ")"
# syntax MappingType   ::= "%mapT"    "(" Type "," Type ")"
# syntax ByteArrayType ::= "%bytesT"  "(" Int ")"
# syntax UnitType      ::= "%unitT" "(" PureNumType "," Unit "," Bool /*positional*/ ")"
# syntax StructType    ::= "%structT" "(" AnnVars ")"
#
# example:
#   %mapT(%num256, %address)
# struct:
#   {f1:num, f2:num}
def parseType(node):
    if node is None:
        return "%void"
    elif type(node) == ast.Name:
        return parseBaseType(node)
    elif type(node) == ast.Compare and type(node.left) == ast.Name and node.left.id == "bytes":
        return "%bytesT({})".format(node.comparators[0].n)  # obsolete
    elif type(node) == ast.Subscript:
        if type(node.slice.value) == ast.Num:
            if type(node.value) == ast.Name and node.value.id == "bytes":
                return "%bytesT({})".format(parseConst(node.slice.value))
            else:
                return "%listT({}, {})".format(parseType(node.value), parseConst(node.slice.value))
        else:
            return "%mapT({}, {})".format(parseType(node.slice.value), parseType(node.value))
    elif type(node) == ast.Dict:
        return "%structT({})".format(parseAnnVars(node))
    elif type(node) == ast.Call:  # part of UnitType
        if isinstance(node.args[-1], ast.Name) and node.args[-1].id == "positional":
            positional = "true"
        else:
            positional = "false"
        if type(node.args[0]) == ast.Name and node.args[0].id == "uint256":
            return "%castT({}, {})".format(parseType(node.func), parseType(node.args[0]))
        elif type(node.func) == ast.Name and (node.func.id == "contract" or node.func.id == "address"):
            return "%contractT({})".format(node.args[0].id)
        else:
            return "%unitT({}, {}, {})".format(parseType(node.func), parseUnit(node.args[0]), positional)
    elif type(node) == ast.Tuple:
        return "%tupleT({})".format(parseList(node.elts, parseType, " "))
    else:
        raise ParserException("Type parsing not yet implemented for: " + str(node))


# EventParam ::= "%eparam" "(" Id "," Type "," Bool /*indexed?*/ ")"
# example:
#   _from: indexed(address)
#   =>
#   %eparam(_from, %address, true)
def parseEventParam(key, value):  # value is Call
    if type(value) == ast.Call and value.func.id == "indexed":
        indexed = "true"
        typeNode = value.args[0]
    else:
        indexed = "false"
        typeNode = value
    return "%eparam({}, {}, {})".format(key.id, parseType(typeNode), indexed)


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
    all_annotations = {"public", "private", "modifiable", "static"}
    annotations = set()
    typeAST = node.annotation
    while type(typeAST) == ast.Call and typeAST.func.id in all_annotations:
        annotations.add(typeAST.func.id)
        typeAST = typeAST.args[0]
    n_type = parseType(typeAST)
    public = "public" in annotations
    modifiable = "modifiable" in annotations
    return "  %svdecl({}, {}, {}, {})".format(node.target.id, n_type,
                                              parseBool(public), parseBool(modifiable))


def parseBool(myBool):
    return str(myBool).lower()


#    syntax Decorator  ::= "%@constant" | "%@payable" | "%@private" | "%@public"
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
    # noinspection PyTypeChecker
    return parseList(args, parseParam, " ")


# syntax Var      ::= "%var"  "(" Id ")"
#                   | "%svar" "(" Id ")"
#                   | AttributeVar
#                   | SubscriptVar
#
# syntax AttributeVar  ::= "%attribute" "(" Var "," Id   ")"  // struct field access
#
# syntax SubscriptVar  ::= "%subscript" "(" Var "," Expr ")"  // list or map element
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
            return "%attribute({}, {})".format(parseVar(var.value), var.attr)
    elif type(var) == ast.Subscript:
        return "%subscript({}, {})".format(parseVar(var.value), parseExpr(var.slice))
    else:
        raise ParserException("Unsupported Var format: " + str(var))


# taken from vyper compiler.
DECIMAL_DIVISOR = 10000000000


def parseFixed10Const(node: ast.Num):
    num, den = get_number_as_fraction(node)
    return "%fixed10({}, {})".format(num, den)


# syntax Const    ::= Int
#                   | "%hex"     "(" String ")"
#                   | "%fixed10" "(" Int "," Int ")"  // decimal fixed point value with a precision of 10 decimal places
#                                                     // %fixed10(A, B) = A/B and B is a power of 10.
#                   | String
#                   | Bool
#
# additional: None
def parseConst(node):
    constConstantMap = {True: "true", False: "false", None: "%None"}
    nameConstantMap = {"true": "true", "false": "false", "null": "%None"}
    if type(node) == ast.Num and type(node.n) == int:
        hexFormat = get_original_if_0x_prefixed(node)
        if hexFormat is None:
            return str(node.n)
        else:
            return "%hex(\"{}\")".format(hexFormat[2:])
    elif type(node) == ast.Num and type(node.n == float):
        return parseFixed10Const(node)
    elif type(node) == ast.Str:
        # return get_original_str(node)
        return "\"{}\"".format(escapeSpecialChars(node.s))
    elif type(node) == ast.NameConstant:
        return constConstantMap[node.value]
    elif type(node) == ast.Name:
        return nameConstantMap[node.id]
    else:
        raise ParserException("Unsupported Const format: " + str(node))


def escapeSpecialChars(s: str):
    translated = s.translate(str.maketrans({"\t": r"\t", "\n": r"\n", "\r": r"\r", "\\": r"\\", "\"": r"\""}))
    encoded = translated.encode('ascii', 'backslashreplace').decode("ascii")
    for i in range(0, 32):
        encoded = encode_char(encoded, i)
    encoded = encode_char(encoded, 127)
    return encoded


def encode_char(encoded, i):
    return encoded.replace(chr(i), '\\x{:02x}'.format(i))


#    syntax Expr :== ...
#                    "%icall"     "(" Id        "," Exprs ")"
#
#     syntax ReservedFunc  ::= "%floor"               "(" Expr ")"
#                           | "%decimal"             "(" Expr ")"
#                           | "%as_unitless_number"  "(" Expr ")"
#                           | "%as_num128"           "(" Expr ")"
#                           | "%as_num256"           "(" Expr ")"
#                           | "%as_bytes32"          "(" Expr ")"
#                           | "%slice"               "(" Expr "," Expr "," Expr ")"
#                           | "%len"                 "(" Expr ")"
#                           | "%concat"              "(" Exprs ")"
#                           | "%keccak256"           "(" Expr ")"
#                           | "%method_id"           "(" Expr ")"
#                           | "%ecrecover"           "(" Expr ")"
#                           | "%ecadd"               "(" Expr "," Expr ")"
#                           | "%ecmul"               "(" Expr "," Expr ")"
#                           | "%extract32"           "(" Expr "," Expr "," Id ")"
#                           | "%bytes_to_num"        "(" Expr ")"
#                           | "%as_wei_value"        "(" Expr "," Id   ")"
#                        // | "%raw_call"            "(" Expr "," Expr "," Expr "," Expr "," Expr ")"
#                           | "%RLPlist"             "(" Expr "," Expr ")"
#                           | "%blockhash"           "(" Expr ")"
#                           | "%bitwise_and"         "(" Expr "," Expr ")"
#                           | "%bitwise_or"          "(" Expr "," Expr ")"
#                           | "%bitwise_xor"         "(" Expr "," Expr ")"
#                           | "%bitwise_not"         "(" Expr ")"
#                           | "%num256_add"          "(" Expr "," Expr ")"
#                           | "%num256_sub"          "(" Expr "," Expr ")"
#                           | "%num256_mul"          "(" Expr "," Expr ")"
#                           | "%num256_div"          "(" Expr "," Expr ")"
#                           | "%num256_exp"          "(" Expr "," Expr ")"
#                           | "%num256_mod"          "(" Expr "," Expr ")"
#                           | "%num256_addmod"       "(" Expr "," Expr "," Expr ")"
#                           | "%num256_mulmod"       "(" Expr "," Expr "," Expr ")"
#                           | "%num256_gt"           "(" Expr "," Expr ")"
#                           | "%num256_ge"           "(" Expr "," Expr ")"
#                           | "%num256_lt"           "(" Expr "," Expr ")"
#                           | "%num256_le"           "(" Expr "," Expr ")"
#                           | "%shift"               "(" Expr "," Expr ")"
#                        // | "%create_with_code_of" "(" Expr "," Expr ")"
#                           | "%min"                 "(" Expr "," Expr ")"
#                           | "%max"                 "(" Expr "," Expr ")"
#                           | "%sha3"                "(" Expr ")"
#
# example:
#   %as_num256(%msg.value)
#
#   num256_add(self.balances[_sender], _value)
#   =>
#   %num256_add(%subscript(%svar(balances), %var(_sender)), %var(_value))
#
#   %as_wei_value(%as_num128(%var(_value)), wei)
#
#   self.raw_call(0x1234567890123456789012345678901234567890, "cow", outsize=4, gas=595757)
def parseCallExpr(expr: ast.Call):
    if type(expr.func) == ast.Name:
        if expr.func.id == "as_wei_value":
            if type(expr.args[1]) == ast.Str:
                return "%as_wei_value({}, {})".format(parseExpr(expr.args[0]), expr.args[1].s)
            else:
                raise KVTypeMismatchException("Expecting str_literal for argument 2 of as_wei_value")
        elif expr.func.id == "concat":
            return "%concat({})".format(parseArgs(expr.args + expr.keywords))
        elif expr.func.id == "raw_call":
            valueArg = getKeyword(expr.keywords, "value")
            value = parseArg(valueArg) if valueArg is not None else "%as_wei_value(0, wei)"
            return "%raw_call({}, {}, {}, {}, {})".format(parseArg(expr.args[0]), parseArg(expr.args[1]),
                                                          parseArg(getKeyword(expr.keywords, "outsize")),
                                                          parseArg(getKeyword(expr.keywords, "gas")),
                                                          value)
        elif expr.func.id == "create_with_code_of":
            valueArg = getKeyword(expr.keywords, "value")
            value = parseArg(valueArg) if valueArg is not None else "%as_wei_value(0, wei)"
            return "%create_with_code_of({}, {})".format(parseArg(expr.args[0]), value)
        elif expr.func.id == "extract32":
            if len(expr.keywords) == 0:
                typeArg = "%bytes32"
            else:
                typeArg = parseBaseType(expr.keywords[0].value)
            return "%extract32({}, {}, {})".format(parseArg(expr.args[0]), parseArg(expr.args[1]), typeArg)
        elif expr.func.id == "RLPList":
            return "%RLPList({}, {})".format(parseArg(expr.args[0]), parseTypes(expr.args[1].elts))
        else:
            return "%{}({})".format(expr.func.id, parseArgs(expr.args + expr.keywords, ", "))
    elif type(expr.func) == ast.Attribute:
        if type(expr.func.value) == ast.Name and expr.func.value.id == "self":
            return "%icall({}, {})".format(expr.func.attr, parseArgs(expr.args + expr.keywords))
        elif type(expr.func.value) == ast.Call:
            return "%ecall({}, {}, {}, {})" \
                .format(expr.func.value.func.id, parseExpr(expr.func.value.args[0]), expr.func.attr,
                        parseArgs(expr.args + expr.keywords))
        elif type(expr.func.value) == ast.Attribute:
            return "%ecall({}, {}, {})" \
                .format(parseExpr(expr.func.value), expr.func.attr, parseArgs(expr.args + expr.keywords))
        else:
            raise ParserException("Unsupported Call Expr format: " + str(expr))
    else:
        raise ParserException("Unsupported Call Expr format: " + str(expr))


def parseTypes(list):
    return parseList(list, parseType, " ")


def getKeyword(keywords: list, param: str):
    for kw in keywords:
        if kw.arg == param:
            return kw.value
    return None


# syntax ReservedExpr  ::= "%msg.sender" | "%msg.value" | "%msg.gas"
#                        | "%block.difficulty" | "%block.timestamp" | "%block.coinbase" | "%block.number"
#                        | "%block.prevhash"
#                        | "%tx.origin"
#
# If no reserved expression found, returns None.
def tryParseReservedExpr(expr: ast.Attribute):
    optionsMap = {"msg": ["sender", "value", "gas"],
                  "block": ["difficulty", "timestamp", "coinbase", "number", "prevhash"],
                  "tx": ["origin"]}
    if type(expr.value) == ast.Name and expr.value.id in optionsMap.keys() \
            and expr.attr in optionsMap.get(expr.value.id):
        return "%" + expr.value.id + "." + expr.attr
    elif expr.attr in ["balance", "codesize", "is_contract"]:
        return "%{}({})".format(expr.attr, parseExpr(expr.value))
    return None


# syntax BinOp         ::= "+" | "-" | "*" | "/" | "%" | "**"
#
# we'll support all operators from Python.
def parseBinOp(op: ast.operator):
    binOpMap = {ast.Add: "+",
                ast.BitAnd: "&",
                ast.BitOr: "|",
                ast.BitXor: "^",
                ast.Div: "/",
                ast.FloorDiv: "//",
                ast.LShift: "<<",
                ast.MatMult: "@",
                ast.Mod: "%",
                ast.Mult: "*",
                ast.Pow: "**",
                ast.RShift: ">>",
                ast.Sub: "-"
                }
    if binOpMap[type(op)] is not None:
        return binOpMap[type(op)]
    else:
        raise ParserException("Unsupported BinOp: " + str(op) + " in " + inputLines[op.lineno][op.col_offset:])


# syntax CompareOp     ::= "%lt" | "%le" | "%gt" | "%ge" | "%eq" | "%ne" | "%in"
def parseCompareOp(op: ast.cmpop):
    compareOpMap = {ast.Eq: "%eq",
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
    if compareOpMap[type(op)] is not None:
        return compareOpMap[type(op)]
    else:
        raise ParserException("Unsupported CompareOp: " + str(op) + " in " + inputLines[op.lineno][op.col_offset:])


# syntax BoolOp        ::= "%and" | "%or"
def parseBoolOp(op: ast.boolop):
    boolOpMap = {ast.And: "%and",
                 ast.Or: "%or",
                 }
    if boolOpMap[type(op)] is not None:
        return boolOpMap[type(op)]
    else:
        raise ParserException("Unsupported BoolOp: " + str(op) + " in " + inputLines[op.lineno][op.col_offset:])


# syntax UnaryOp       ::= "%not" | "%neg"
def parseUnaryOp(op: ast.unaryop):
    unaryOpMap = {ast.Invert: None,
                  ast.Not: "%not",
                  ast.UAdd: None,
                  ast.USub: "%neg",
                  }
    if unaryOpMap[type(op)] is not None:
        return unaryOpMap[type(op)]
    else:
        raise ParserException("Unsupported UnaryOp: " + str(op) + " in " + inputLines[op.lineno][op.col_offset:])


# syntax StructItem    ::= "%item" "(" Id "," Expr ")"
# syntax StructItems   ::= List{StructItem, ""}
def parseStructItems(node):
    rez = ""
    for i in range(0, len(node.keys)):
        key = node.keys[i]
        value = node.values[i]
        if rez != "":
            rez += " "
        rez += "%item({}, {})".format(key.id, parseExpr(value))
    return rez


# syntax Expr     ::= Const
#                   | Var
#                   | ListExpr
#                   | StructExpr
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
# syntax StructExpr    ::= "%struct" "(" StructItems ")"
#
# examples:
#   %var(_sender)
#   %as_num256(%msg.value)
#   %msg.value
#   %subscript(%svar(balances), %var(_sender))
#   %binop(+, %var(x), 10)
def parseExpr(node):
    if type(node) == ast.Index:
        return parseExpr(node.value)
    elif type(node) == ast.Num or type(node) == ast.Str or type(node) == ast.NameConstant \
            or (type(node) == ast.Name and node.id in ["true", "false", "null"]):
        return parseConst(node)
    elif type(node) == ast.Name and node.id == "self":
        return "%self"
    elif type(node) == ast.BinOp:
        return "%binop({}, {}, {})".format(parseBinOp(node.op), parseExpr(node.left), parseExpr(node.right))
    elif type(node) == ast.Compare:
        if len(node.ops) > 1 or len(node.comparators) > 1:
            raise ParserException("Unsupported complex comparator format: " + inputLines[node.lineno][node.col_offset:])
        return "%compareop({}, {}, {})" \
            .format(parseCompareOp(node.ops[0]), parseExpr(node.left), parseExpr(node.comparators[0]))
    elif type(node) == ast.BoolOp:
        if in_assignment and (type(node.values[0]) == ast.Call or type(node.values[1]) == ast.Call):
            raise KVStructureException("Boolean operations with calls may not be performed on assignment")
        return "%boolop({}, {}, {})".format(parseBoolOp(node.op), parseExpr(node.values[0]), parseExpr(node.values[1]))
    elif type(node) == ast.UnaryOp:
        return "%unaryop({}, {})".format(parseUnaryOp(node.op), parseExpr(node.operand))
    elif type(node) == ast.Attribute:
        rez = tryParseReservedExpr(node)
        if rez is not None:
            return rez
        else:
            return parseVar(node)
    elif type(node) == ast.Name or type(node) == ast.Subscript:
        return parseVar(node)
    elif type(node) == ast.List:
        return "%list({})".format(parseExprs(node.elts))
    elif type(node) == ast.Dict:
        return "%struct({})".format(parseStructItems(node))
    elif type(node) == ast.Call:
        return parseCallExpr(node)
    elif type(node) == ast.Tuple:
        return "%tuple({})".format(parseExprs(node.elts))
    else:
        raise ParserException("Unsupported Expr format: " + str(node))


# syntax Exprs  ::= List{Expr, ""}
def parseExprs(exprs, separator=" "):
    return parseList(exprs, parseExpr, separator)


# syntax Argument  ::= Expr
#                    | "%kwarg" "(" Id "," Expr ")"
def parseArg(node):
    if type(node) == ast.keyword:
        return parseExpr(node.value)
    else:
        return parseExpr(node)


# syntax Arguments ::= List{Argument, ""}
def parseArgs(args, separator=" "):
    return parseList(args, parseArg, separator)


# syntax AugAssignOp ::= "+=" | "-=" | "*=" | "/=" | "%="
def parseAugAssignOp(op: ast.operator):
    return "{}=".format(parseBinOp(op))


# syntax AnnVar  ::= "%annvar" "(" Id "," Type ")"
#
# ex: %annvar(a, %listT(%num, 5))
# 3-arg annvar:
#   z: int128 = x
def parseAnnVar(stmt: ast.AnnAssign):
    if stmt.value is None:
        return parseAnnVarKeyValue(stmt.target, stmt.annotation)
    else:
        return "%annvar({}, {}, {})".format(stmt.target.id, parseType(stmt.annotation), parseExpr(stmt.value))


def parseAnnVarKeyValue(key, value):
    return "%annvar({}, {})".format(key.id, parseType(value))


# syntax AnnVars ::= List{AnnVar, ""}
def parseAnnVars(annVars: ast.Dict):
    return parseDict(annVars, parseAnnVarKeyValue, " ")


in_assignment = False


# syntax Stmt     ::= AnnVar
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
#                   | "%stmtexpr"  "(" Expr ")"
#                   // stmt dispatch table
#                   | "%send"      "(" Expr "," Expr ")"
#                   | "%selfdestruct" "(" Expr ")"
#                   | "%rawlog"    "(" Expr "," Expr ")"
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
def parseStmt(node):
    if type(node) == ast.AnnAssign or type(node) == ast.Assign or type(node) == ast.AugAssign:
        global in_assignment
        in_assignment = True

        if type(node) == ast.AnnAssign:
            result = parseAnnVar(node)
        elif type(node) == ast.Assign:
            result = "%assign({}, {})".format(parseVar(node.targets[0]), parseExpr(node.value))
        elif type(node) == ast.AugAssign:
            result = "%augassign({}, {}, {})".format(parseAugAssignOp(node.op), parseVar(node.target),
                                                     parseExpr(node.value))
        else:
            raise ParserException("unreachable")
        in_assignment = False
        return result

    elif type(node) == ast.If:
        if len(node.orelse) == 0:
            return "%if({},{})".format(parseExpr(node.test), parseStmts(node.body))
        else:
            return "%if({},{},{})".format(parseExpr(node.test), parseStmts(node.body), parseStmts(node.orelse))
    elif type(node) == ast.For:
        if type(node.iter) == ast.Call and type(node.iter.func) == ast.Name and node.iter.func.id == "range":
            if len(node.iter.args) == 1:
                return "%forrange({}, {},{})".format(node.target.id, parseExpr(node.iter.args[0]),
                                                     parseStmts(node.body))
            else:
                return "%forrange({}, {}, {},{})".format(node.target.id, parseExpr(node.iter.args[0]),
                                                         parseExpr(node.iter.args[1]), parseStmts(node.body))
        else:  # every for that's not "for in range()" is parsed as %forlist
            return "%forlist({}, {},{})".format(node.target.id, parseExpr(node.iter), parseStmts(node.body))
    elif type(node) == ast.Break:
        return "%break"
    elif type(node) == ast.Continue:
        return "%continue"
    elif type(node) == ast.Pass:
        return "%pass"
    elif type(node) == ast.Return:
        if node.value is None:
            return "%return"
        else:
            return "%return({})".format(parseExpr(node.value))
    elif type(node) == ast.Assert:
        return "%assert({})".format(parseExpr(node.test))
    elif type(node) == ast.Delete:
        return "%del({})".format(parseExpr(node.targets[0]))
    elif type(node) == ast.Expr and type(node.value) == ast.Name and node.value.id == "throw":
        return "%throw"
    elif type(node) == ast.Expr and type(node.value) == ast.Call:
        if type(node.value.func) == ast.Attribute and type(node.value.func.value) == ast.Name \
                and node.value.func.value.id == "log":
            return "%log({}, {})".format(node.value.func.attr, parseArgs(node.value.args))
        elif type(node.value.func) == ast.Name and node.value.func.id == "send":
            return "%send({})".format(parseArgs(node.value.args, ", "))
        elif type(node.value.func) == ast.Name and node.value.func.id == "selfdestruct":
            return "%selfdestruct({})".format(parseArgs(node.value.args, ", "))
        else:
            return "%stmtexpr({})".format(parseExpr(node.value))
    else:
        raise ParserException("Unsupported Stmt format: " + str(node))


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
def parseDef(node: ast.FunctionDef, doubleIndent=False):
    template = "  %fdecl({}, {}, {}, {},{})"
    if doubleIndent:
        global stmtsIndent
        stmtsIndent = "    "
        template = "  " + template

    return template.format(
        parseDecorators(node.decorator_list),
        node.name,
        parseParams(node.args.args),
        parseType(node.returns),
        parseStmts(node.body)
    )


#    syntax Contract ::= "%contract" "(" Id   //contract name
#                                    "," Defs //contract functions
#                                    ")"
# noinspection PyTypeChecker
def parseContract(contract: ast.ClassDef):
    _contractname = contract.name
    _contract_defs = contract.body
    _defnames = [_def.name for _def in _contract_defs]
    if len(set(_defnames)) < len(_contract_defs):
        raise ParserException(
            "Duplicate function name: %s" % [name for name in _defnames if _defnames.count(name) > 1][0])
    fdecls = parseList(_contract_defs, parseDef, "\n", "\n", " ", True)
    return "  %contract({},{}\n  )".format(_contractname, fdecls)


# Pgm ::= "%pgm" "(" Events "," Globals "," Defs ")"
# noinspection PyTypeChecker
def parseProgram(nodeList):
    _events = []
    _globals = []
    _init = []
    _defs = []
    _contracts = []
    for node in nodeList:
        if type(node) == ast.AnnAssign and type(node.annotation) == ast.Call and node.annotation.func.id == "event":
            _events.append(node)
        elif type(node) == ast.AnnAssign:
            _globals.append(node)
        elif type(node) == ast.FunctionDef:
            if node.name == "__init__":
                _init.append(node)
            else:
                _defs.append(node)
        elif type(node) == ast.ClassDef:
            _contracts.append(node)
        else:
            raise ParserException("Unsupported top level node: " + str(node))

    if _init:
        return "%pgm({},{},{},{},{}\n)".format(
            parseList(_events, parseEvent, "\n", "\n"),
            parseList(_globals, parseGlobal, "\n", "\n", " "),
            parseList(_init, parseDef, "\n", "\n", " "),
            parseList(_defs, parseDef, "\n", "\n", " "),
            parseList(_contracts, parseContract, "\n", "\n", " "))
    else:
        return "%pgm({},{},{},{}\n)".format(
            parseList(_events, parseEvent, "\n", "\n"),
            parseList(_globals, parseGlobal, "\n", "\n", " "),
            parseList(_defs, parseDef, "\n", "\n", " "),
            parseList(_contracts, parseContract, "\n", "\n", " "))


inputLines: List[str]


def main(vyperPgm):
    global inputLines
    inputLines = vyperPgm.splitlines()
    if "ERC20" in vyperPgm:
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "premade_contracts.v.py"), "r") as fin:
            premadeContracts = fin.read()
        vyperPgm += "\n" + premadeContracts

    pythonAST = parse(vyperPgm)
    program = parseProgram(pythonAST)
    return program


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("One argument expected: the file name.")
        sys.exit(1)
    fileName = sys.argv[1]
    with open(fileName, "r") as fin:
        vyperPgm = fin.read()
    print(main(vyperPgm))
