require "viper-lll-interface.k"
require "viper-config.k"
require "utils.k"
require "domains.k"

module VIPER-LLL
    imports VIPER-LLL-INTERFACE
    imports VIPER-SYNTAX
    imports LLL-SYNTAX
    imports VIPER-CONFIG
    imports UTILS
    imports STRING
    imports KRYPTO


    syntax TypedAddr ::= "@taddr" "(" Type ","
                                      LLLExp /*location*/ ","
                                      Bool   /*global*/   ","
                                      Bool   /*mutable*/  ")"

    syntax TypedLLLExp  ::= "@tlll"  "(" Type "," LLLExp ")"
    syntax TypedLLLExps ::= "@tllls" "(" Type "," LLLExp ")"


    // Convention: C'Sort' is an one-one corresponding supersort of Sort which
    //             requires for evaluation (i.e. not KResult).
    syntax CLLLExp  ::= LLLExp
    syntax CLLLExps ::= LLLExps
    syntax CTypedLLLExp  ::= TypedLLLExp
    syntax CTypedLLLExps ::= TypedLLLExps
    syntax CType    ::= Type
    syntax CTypedAddr ::= TypedAddr


    syntax KResult  ::= LLLExp
                      | LLLExps
                      | TypedLLLExp
                      | TypedLLLExps
                      | TypedAddr
                      | Type
                      | Bool
                      | Int
   

    syntax KItem    ::= "#compileViperToLLL"    "(" Pgm ")"
    syntax KItem    ::= "#compileViperToLLLAux" "(" CLLLExps /*initializer*/  ","
                                                    CLLLExps /*init func*/    ","
                                                    CLLLExps /*regular func*/ ","
                                                    CLLLExps /*public getter*/
                                                 ")"                  [seqstrict]
    syntax KItem    ::= "#compileViperToLLLAux" "(" CLLLExps /*initializer*/  ","
                                                    CLLLExps /*regular func*/ ","
                                                    CLLLExps /*public getter*/
                                                ")"                   [seqstrict]
 // ----------------------------------------------------------------------------
    rule #compileViperToLLL(%pgm(GS, INIT, DEFS)) => #resolveGlobals(GS)
                                                  ~> #compileViperToLLLAux(
                                                         #initializer_lll,
                                                         #resolveFunc(INIT),
                                                         #resolveFuncs(DEFS),
                                                         #resolveFuncs(#mkPublicGetters(GS, .Defs)))

    rule #compileViperToLLL(%pgm(GS, DEFS)) => #resolveGlobals(GS)
                                            ~> #compileViperToLLLAux(
                                                   #initializer_lll,
                                                   #resolveFuncs(DEFS),
                                                   #resolveFuncs(#mkPublicGetters(GS, .Defs)))


    rule <k> #compileViperToLLLAux(INITIALIZER, INITFUNC, OTHERFUNCS, PUBLICGETTERS) => . ... </k>
         <lll> _ => $%seq(
                      $%seq(INITIALIZER) ++LLL INITFUNC ++LLL
                      $return(
                        0,
                        $lll($%seq(INITIALIZER ++LLL OTHERFUNCS ++LLL PUBLICGETTERS), 0));.LLLExps) </lll>

    rule <k> #compileViperToLLLAux(INITIALIZER, OTHERFUNCS, PUBLICGETTERS) => . ... </k>
         <lll> _ => $%seq(
                      $return(
                        0,
                        $lll($%seq(INITIALIZER ++LLL OTHERFUNCS ++LLL PUBLICGETTERS ), 0));.LLLExps) </lll>


    syntax KItem     ::= "#resolveGlobals" "(" Globals ")"
 // ------------------------------------------------------
    rule #resolveGlobals(.Globals) => .

    rule <k> #resolveGlobals(%svdecl(NAME, T, _) GS) => #resolveGlobals(GS) ... </k>
         <global> GLOBAL => GLOBAL[%svar(NAME) <- @taddr(T, LOC, true, true)] </global>
         <nextStorage> LOC => LOC +Int 1 </nextStorage>


    syntax CLLLExps ::= "#extendLLL" "(" CLLLExps "," CLLLExps ")"       [seqstrict]
 // --------------------------------------------------------------------------------
    rule #extendLLL(C1:LLLExps, C2:LLLExps) => C1 ++LLL C2


    syntax CLLLExps ::= "#resolveFuncs"    "(" Defs ")"
    syntax CLLLExps ::= "#resolveFuncsAux" "(" Defs "," CLLLExps ")"  [strict(2)]
 // -----------------------------------------------------------------------------
    rule #resolveFuncs(DEFS) => #resolveFuncsAux(DEFS, .LLLExps)
    rule #resolveFuncsAux(.Defs, CODE) => CODE
    rule #resolveFuncsAux(DEF DEFS, CODE) => #resolveFuncsAux(DEFS, #extendLLL(CODE, #resolveFunc(DEF)))


    syntax CLLLExps ::= "#resolveFunc"    "(" Def  ")"
    syntax CLLLExps ::= "#resolveFuncAux" "(" CLLLExps /*copy input*/      ","
                                              CLLLExps /*check decorator*/ ","
                                              CLLLExps /*fill params*/     ","
                                              CLLLExps /*resolve stmts*/   ","
                                              Int      /*method id*/       ","
                                              Bool     /*is init?*/
                                          ")"                      [seqstrict]
 // --------------------------------------------------------------------------
    rule <k> #resolveFunc(%fdecl(DECS, NAME, PARAMS, T, STMTS))
                 => #resolveFuncAux(#copyInput(PARAMS, #isInitFunc(NAME)),
                                    #checkDecorators(DECS),
                                    #fillParams(PARAMS, 0, #isInitFunc(NAME)),
                                    #resolveStmts(STMTS),
                                    #generateMethodId(NAME, PARAMS),
                                    #isInitFunc(NAME))
                 ~> #cleanConfig ... </k>
         <return> _ => T </return>


    rule #resolveFuncAux(COPYINPUT, CHECKDECS, FILLPARAMS, STMTS, _, true)
             => $%seq(COPYINPUT ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL $%seq(STMTS));.LLLExps

    rule #resolveFuncAux(COPYINPUT, CHECKDECS, FILLPARAMS, STMTS, METHODID, false)
             => $if(
                  $eq($mload(0), METHODID),
                  $%seq(COPYINPUT ++LLL CHECKDECS ++LLL FILLPARAMS ++LLL STMTS ++LLL $stop));.LLLExps


    syntax CLLLExps ::= "#copyInput" "(" Params "," Bool /*is init?*/ ")"
 // ---------------------------------------------------------------------
    rule #copyInput(.Params, _) => $pass;.LLLExps

    rule <k> #copyInput(PARAMS, true) => $codecopy(#reservedMemPos,
                                                   $codelen, 
                                                   #sizeOfParams(PARAMS));.LLLExps ... </k>
         <nextMem> M => M +Int #sizeOfParams(PARAMS) </nextMem>
      requires #sizeOfParams(PARAMS) >Int 0

    rule <k> #copyInput(PARAMS, false) => $calldatacopy(#reservedMemPos, 
                                                        4, 
                                                        #sizeOfParams(PARAMS));.LLLExps ... </k>
         <nextMem> M => M +Int #sizeOfParams(PARAMS) </nextMem>
      requires #sizeOfParams(PARAMS) >Int 0


    syntax CLLLExps ::= "#checkDecorators" "(" Decorators ")"
    syntax CLLLExps ::= "#checkConstant"   "(" Decorators ")"
    syntax CLLLExps ::= "#checkPayable"    "(" Decorators ")"
    syntax CLLLExps ::= "#checkInternal"   "(" Decorators ")"
 // ---------------------------------------------------------
    rule #checkDecorators(DECS) => #extendLLL(
                                       #checkConstant(DECS),
                                       #extendLLL(
                                           #checkPayable(DECS),
                                           #checkInternal(DECS)))

    rule <k> #checkConstant(DECS) => .LLLExps ... </k>
         <constant> _ => true </constant>
      requires #inDecorators(%@constant, DECS)

    rule <k> #checkConstant(DECS) => .LLLExps ... </k>
         <constant> _ => false </constant>
      requires notBool #inDecorators(%@constant, DECS)

    rule <k> #checkPayable(DECS) => .LLLExps ... </k>
         <payable> _ => true </payable>
      requires #inDecorators(%@payable, DECS)

    rule <k> #checkPayable(DECS) => $assert($iszero($callvalue));.LLLExps ... </k>
         <payable> _ => false </payable>
      requires notBool #inDecorators(%@payable, DECS)

    rule <k> #checkInternal(DECS) => $assert($eq($caller, $address));.LLLExps ... </k>
      requires #inDecorators(%@internal, DECS)

    rule #checkInternal(DECS) => .LLLExps
      requires notBool #inDecorators(%@internal, DECS)


    syntax CLLLExps ::= "#fillParam"  "(" Param  "," Int "," Bool ")"
    syntax CLLLExps ::= "#fillParams" "(" Params "," Int /*data pos*/ "," Bool")"
 // --------------------------------------------------------------------------------
    rule <k> #fillParam(%param(NAME, %bytes(L)), DATAPOS, ISINIT) => #mkClamper(%bytes(L), DATAPOS, LOC, ISINIT) ... </k>
         <env> ENV => #updateEnv(%var(NAME), %bytes(L), LOC, ENV, false)</env>
         <nextMem> LOC => LOC +Int #sizeOfType(%bytes(L)) </nextMem>

    rule <k> #fillParam(%param(NAME, T), DATAPOS, ISINIT) => #mkClamper(T, DATAPOS, LOC, ISINIT) ... </k>
         <env> ENV => #updateEnv(%var(NAME), T, #reservedMemPos +Int DATAPOS, ENV, false) </env>
         <nextMem> LOC </nextMem>
      requires notBool isByteArrayType(T)

    rule #fillParams(.Params, _, _) => .LLLExps

    rule #fillParams(P PS, DATAPOS, ISINIT)
             => #extendLLL(#fillParam(P, DATAPOS, ISINIT), #fillParams(PS, DATAPOS +Int #sizeOfParam(P), ISINIT))


 ///////////////////////////////////////////////////////////////////////////////
 // Stmts
 ///////////////////////////////////////////////////////////////////////////////


    syntax CLLLExps ::= "#resolveStmts"    "(" Stmts ")"
    syntax CLLLExps ::= "#resolveStmtsAux" "(" Stmts "," CLLLExps ")"  [strict(2)]
 // ------------------------------------------------------------------------------
    rule #resolveStmts(STMTS) => #resolveStmtsAux(STMTS, .LLLExps)

    rule #resolveStmtsAux(.Stmts, CODE) => CODE

    rule #resolveStmtsAux(STMT STMTS, CODE) => #resolveStmtsAux(STMTS, #extendLLL(CODE, #resolveStmt(STMT)))


    syntax CLLLExps ::= "#resolveStmt"     "(" Stmt ")"
 // -------------------------------------------------------
    rule #resolveStmt(%break) => $break; .LLLExps

    rule #resolveStmt(%pass) => $pass;.LLLExps

    rule #resolveStmt(%throw) => $assert(0);.LLLExps


    // Assign
    syntax CLLLExps ::= "#assign"    "(" Var                             ","
                                         CTypedLLLExp  /*compiled Expr*/
                                     ")"                         [strict(2)]
    syntax CLLLExps ::= "#assignAux" "(" CTypedAddr /*variable address*/ ","
                                         TypedLLLExp
                                     ")"                         [strict(1)]
 // ------------------------------------------------------------------------
    rule #resolveStmt(%assign(V, E)) => #assign(V, #resolveExpr(E))

    rule #assign(V, @tlll(T, CODE)) => #assignAux(#lookupOrAllocVar(V, T), @tlll(T, CODE))

    rule <k> #assignAux(@taddr(LT, LOC, ISGLOBAL, ISMUTABLE), RTCODE)
                 => #ifThen((ISGLOBAL ==K true andBool ISCONSTANT ==K true),
                            #exception("Cannot modify storage inside a constant function!"))
                 ~> #ifThen(ISMUTABLE ==K false,
                            #exception("Cannot modify function argument"))
                 ~> #convertToLLLExps(#mkSetter(@taddr(LT, LOC, ISGLOBAL, ISMUTABLE), RTCODE))
                 ... </k>
         <constant> ISCONSTANT </constant>


    syntax CTypedAddr ::= "#lookupOrAllocVar" "(" Var "," Type ")"
 // --------------------------------------------------------------
    rule <k> #lookupOrAllocVar(%var(NAME), _) => TADDR ... </k>
         <env> %var(NAME) |-> TADDR:TypedAddr ENV </env>

    rule <k> #lookupOrAllocVar(%var(NAME), T) => #allocVar(%var(NAME), T) ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in keys(ENV)

    rule #lookupOrAllocVar(%svar(NAME), _) => #lookupVar(%svar(NAME))

    rule #lookupOrAllocVar(%mapelem(V, EXPR), _) => #lookupVar(%mapelem(V, EXPR))


    syntax CTypedAddr ::= "#allocVar" "(" Var "," Type ")"
 // ------------------------------------------------------
    rule <k> #allocVar(%var(NAME), T) => @taddr(T, LOC, false, true) ...</k>
         <env> ENV => #updateEnv(%var(NAME), T, LOC, ENV, true) </env>
         <nextMem> LOC => LOC +Int #sizeOfType(T) </nextMem>
      requires notBool %var(NAME) in keys(ENV)

    rule <k> #allocVar(%var(NAME), T)
                 => #exception("Duplicate variable name: " +String Id2String(NAME)) ...</k>
         <env> ENV </env>
      requires %var(NAME) in keys(ENV)


    syntax CLLLExp ::= "#mkSetter"    "(" TypedAddr    /*left variable address*/   ","
                                          TypedLLLExp  /*right compiled Expr*/
                                      ")"
    syntax CLLLExp ::= "#mkSetterForBase" "("TypedAddr "," CTypedLLLExp ")"    [strict(2)]
 // --------------------------------------------------------------------------------------
    rule #mkSetter(@taddr(LT, LOC, ISGLOBAL, ISMUTABLE), RTCODE)
             => #mkSetterForBase(@taddr(LT, LOC, ISGLOBAL, ISMUTABLE),
                                 #baseTypeConvert(RTCODE, LT))
      requires isBaseType(LT)

    rule #mkSetterForBase(@taddr(_, LOC, true, _), @tlll(_, CODE)) => $sstore(LOC, CODE)

    rule #mkSetterForBase(@taddr(_, LOC, false, _), @tlll(_, CODE)) => $mstore(LOC, CODE)


    // Augassign
    syntax CLLLExps ::= "#augassign"    "(" AugAssignOp                     ","
                                            CTypedAddr /*variable address*/ ","
                                            CTypedLLLExp  /*compiled Expr*/
                                        ")"                    [seqstrict(2,3)]
    syntax CLLLExps ::= "#augassignAux" "(" TypedAddr /*variable address*/  ","
                                            CTypedLLLExp  /*compiled Expr*/
                                        ")"                         [strict(2)]
 // ---------------------------------------------------------------------------
    rule #resolveStmt(%augassign(OP, V, E)) => #augassign(OP, #lookupVar(V), #resolveExpr(E))

    rule <k> #augassign(OP, @taddr(LT, LOC, true, _), RTCODE)
                 => #exception("Cannot modify storage inside a constant function!") ... </k>
         <constant> true </constant>

    rule <k> #augassign(OP, @taddr(LT, LOC, true, ISMUTABLE), RTCODE)
                 => #augassignAux(@taddr(LT, LOC, true, ISMUTABLE),
                                  #baseTypeConvert(
                                      #convertToBinaryArith(OP, @tlll(LT, $sload($stloc)), RTCODE),
                                      LT)) ... </k>
         <constant> false </constant>

    rule <k> #augassign(OP, @taddr(LT, LOC, false, ISMUTABLE), RTCODE)
                 => #augassignAux(@taddr(LT, LOC, false, ISMUTABLE),
                                  #baseTypeConvert(
                                      #convertToBinaryArith(OP, @tlll(LT, $mload($mloc)), RTCODE),
                                      LT)) ... </k>
          <constant> false </constant>

    rule #augassignAux(@taddr(_, LOC, true, _), @tlll(_, CODE))
             => $with($stloc, LOC, $sstore($stloc, CODE));.LLLExps

    rule #augassignAux(@taddr(_, LOC, false, _), @tlll(_, CODE))
             => $with($mloc, LOC, $mstore($mloc, CODE));.LLLExps


    syntax CTypedLLLExp ::= "#convertToBinaryArith" "(" AugAssignOp           ","
                                                        TypedLLLExp  /*left*/ ","
                                                        TypedLLLExp  /*right*/
                                                    ")"
 // ------------------------------------------------------------------------------
    rule #convertToBinaryArith(+=, LEXP, REXP) => #binOp(+, LEXP, REXP)


    // if
    syntax CLLLExps ::= "#if" "(" CTypedLLLExp /*TEST*/ ","
                                  CLLLExps     /*Then*/ ","
                                  CLLLExps     /*Else*/
                              ")"               [seqstrict]
    syntax CLLLExps ::= "#if" "(" CTypedLLLExp /*TEST*/ ","
                                  CLLLExps     /*Then*/
                              ")"               [seqstrict]
 // -------------------------------------------------------
    rule #resolveStmt(%if(TEST, THENSTMTS, ELSESTMTS)) => #if(#resolveExpr(TEST),
                                                              #resolveStmts(THENSTMTS),
                                                              #resolveStmts(ELSESTMTS))

    rule #resolveStmt(%if(TEST, THENSTMTS)) => #if(#resolveExpr(TEST), #resolveStmts(THENSTMTS))

    rule #if(@tlll(_, CODE), THEN:LLLExps, ELSE:LLLExps) => $if(CODE, $%seq(THEN), $%seq(ELSE));.LLLExps

    rule #if(@tlll(_, CODE), THEN:LLLExp) => $if(CODE, $%seq(THEN));.LLLExps


    // for
    syntax CLLLExps ::= "#for" "(" CTypedAddr             ","
                                   CTypedLLLExp /*start*/ ","
                                   Int         /*rounds*/ ","
                                   CLLLExps
                               ")"         [seqstrict(1,2,4)]
 // ---------------------------------------------------------
    // e.g. for i in range(10): ...
    rule #resolveStmt(%for(NAME, ROUNDS, STMTS)) => #for(#allocLoopVar(NAME), @tlll(%num, 0), ROUNDS, #resolveStmts(STMTS))

    // e.g. for i in range(100, 110): ...
    rule #resolveStmt(%for(NAME, START:Int, END:Int, STMTS))
             => #for(#allocLoopVar(NAME), @tlll(%num, START), END -Int START, #resolveStmts(STMTS))

    // e.g. for i in range(x, x + 10): ...
    rule #resolveStmt(%for(NAME, %var(V), %binop(+, %var(V), ROUNDS:Int), STMTS))
             => #for(#allocLoopVar(NAME), #resolveExpr(%var(V)), ROUNDS, #resolveStmts(STMTS))

    rule #for(@taddr(%num, LOC:Int, _, _), @tlll(_, STARTCODE), ROUNDS, BODYCODE:LLLExps)
             => $repeat(LOC, STARTCODE, ROUNDS, $%seq(BODYCODE));.LLLExps


    syntax CTypedAddr ::= "#allocLoopVar" "(" Id ")"
 // ------------------------------------------------
    rule <k> #allocLoopVar(NAME) => #lookupVar(%var(NAME)) ... </k>
         <forvar> FORNAMES </forvar>
      requires NAME in FORNAMES

    rule <k> #allocLoopVar(NAME) => #allocVar(%var(NAME), %num) ... </k>
         <forvar> FORNAMES (.Set => SetItem(NAME)) </forvar>
      requires notBool NAME in FORNAMES


    // return
    syntax CLLLExps ::= "#return" "(" CTypedLLLExp "," Type /*return type*/ ")"  [strict(1)]
    syntax CLLLExps ::= "#returnBase" "(" TypedLLLExp "," Type ")"
 // ----------------------------------------------------------------------------------------
    rule <k> #resolveStmt(%return) => #ifThenElse(T =/=K %void,
                                                  #exception("Expecting to return a value"),
                                                  .LLLExps) ... </k>
         <return> T </return>

    rule <k> #resolveStmt(%return(E)) => #ifThenElse(T =/=K %void,
                                                     #return(#resolveExpr(E), T),
                                                     #exception("Not expecting to return a value")) ... </k>
         <return> T </return>

    rule #return(@tlll(T, CODE), RETURNTYPE) => #returnBase(@tlll(T, CODE), RETURNTYPE)
      requires isBaseType(T)

    rule #returnBase(@tlll(T, CODE), RETURNTYPE)
             => #ifThenElse(T ==K RETURNTYPE,
                            $%seq($mstore(0, CODE); $return(0, 32);.LLLExps);.LLLExps,
                            #exception("Unsupported type conversion."))


    // send
    syntax CLLLExps ::= "#send"    "(" CTypedLLLExp /*to*/ "," CTypedLLLExp /*value*/ ")"  [seqstrict]
 // --------------------------------------------------------------------------------------------------
    rule <k> #resolveStmt(%send(TO, VALUE))
                 => #ifThenElse(CONSTANT ==K false,
                                #send(#resolveExpr(TO), #resolveExpr(VALUE)),
                                #exception("Cannot send ether inside a constant function")) ... </k>
         <constant> CONSTANT </constant>

    rule #send(@tlll(%address, TOCODE), @tlll(%unit(%num, %wei, _), VALUECODE))
             => $assert($call(0, TOCODE, VALUECODE, 0, 0, 0, 0)); .LLLExps


    // Type convert
    syntax CTypedLLLExp ::= "#baseTypeConvert" "(" CTypedLLLExp "," Type /*to*/ ")"  [strict(1)]
 // --------------------------------------------------------------------------------------------
    rule #baseTypeConvert(@tlll(FROMT, CODE), TOT)
             => #ifThenElse(notBool(isBaseType(FROMT)) orBool notBool(isBaseType(TOT)),
                            #exception("Base type conversion from or to non-base type."),
                  #ifThenElse(FROMT ==K TOT,
                              @tlll(TOT, CODE),
                    #ifThenElse(FROMT ==K %num andBool TOT ==K %decimal,
                                @tlll(TOT, $mul(CODE, #decimalDivisor)),
                                #exception("Typecasting unavailable"))))


 ///////////////////////////////////////////////////////////////////////////////
 // Expressions
 ///////////////////////////////////////////////////////////////////////////////


    syntax CTypedLLLExp ::= "#resolveExpr" "(" Expr ")"
 // ---------------------------------------------------
    rule #resolveExpr(%self) => @tlll(%address, $address)


    // Number
    rule #resolveExpr(I:Int) => #ifThenElse(
                                  (I >=Int -2 ^Int 127 +Int 1) andBool (I <=Int 2 ^Int 127 -Int 1),
                                  @tlll(%num, I),
                                  #exception("Number out of range")
                                )


    // Bool
    rule #resolveExpr(true)  => @tlll(%bool, 1)

    rule #resolveExpr(false)  => @tlll(%bool, 0)


    // Var
    rule #resolveExpr(V) => #unwrapLocation(#lookupVar(V))


    syntax CTypedAddr ::= "#lookupVar" "(" Var ")"
 // ----------------------------------------------
    rule <k> #lookupVar(%var(NAME)) => TADDR ... </k>
         <env> %var(NAME) |-> TADDR:TypedAddr ENV </env>

    rule <k> #lookupVar(%var(NAME))
                 => #exception("Undeclared Variable: " +String Id2String(NAME)) ... </k>
         <env> ENV </env>
      requires notBool %var(NAME) in keys(ENV)

    rule <k> #lookupVar(%svar(NAME)) => TADDR ... </k>
         <global> %svar(NAME) |-> TADDR:TypedAddr GLOBAL </global>

    rule <k> #lookupVar(%svar(NAME))
                 => #exception("Persistent variable undeclared: " +String Id2String(NAME)) ... </k>
         <global> GLOBAL </global>
      requires notBool %svar(NAME) in keys(GLOBAL)

    rule #lookupVar(%mapelem(V, EXPR))
             => #computeVarOffset(#lookupVar(V), #resolveExpr(EXPR))


    syntax CTypedAddr ::= "#computeVarOffset" "(" CTypedAddr   /*parent*/ ","
                                                  CTypedLLLExp /*key*/
                                              ")"                 [seqstrict]
    syntax CTypedAddr ::= "#computeVarOffsetForMap" "(" CTypedAddr        ","
                                                        CTypedLLLExp
                                                    ")"           [strict(2)]
 // -------------------------------------------------------------------------
    rule #computeVarOffset(@taddr(%map(VT, KT), LOC, GLOBAL, MUTABLE), TCODE)
             => #computeVarOffsetForMap(@taddr(%map(VT, KT), LOC, GLOBAL, MUTABLE),
                                        #baseTypeConvert(TCODE, KT))

    rule #computeVarOffsetForMap(@taddr(%map(VT, KT), LOC, true, MUTABLE), @tlll(_, CODE))
             => @taddr(VT, $add($sha3_32(LOC), CODE), true, MUTABLE)

    rule #computeVarOffsetForMap(@taddr(%map(VT, KT), _, false, _), _)
             => #exception("Can only have fixed-side arrays in memory, not mappings")


    // Reserved Expr
    rule #resolveExpr(%msg.sender)       => @tlll(%address, $caller)

    rule #resolveExpr(%msg.value)        => @tlll(%unit(%num, %wei, false), $callvalue)

    rule #resolveExpr(%msg.gas)          => @tlll(%num, $gas)

    rule #resolveExpr(%block.difficulty) => @tlll(%num, $difficulty)

    rule #resolveExpr(%block.timestamp)  => @tlll(%unit(%num, %sec, true), $timestamp)

    rule #resolveExpr(%block.coinbase)   => @tlll(%address, $coinbase)

    rule #resolveExpr(%block.number)     => @tlll(%num, $number)

    rule #resolveExpr(%block.prevhash)   => @tlll(%bytes32, $blockhash($sub($number, 1)))

    rule #resolveExpr(%tx.origin)        => @tlll(%address, $origin)


    // Reserved Func
    rule #resolveExpr(%as_num128(EXPR)) => #asNum128(#resolveExpr(EXPR))

    rule #resolveExpr(%as_num256(EXPR)) => #asNum256(#resolveExpr(EXPR))

    rule #resolveExpr(%as_wei_value(EXPR, UNIT)) => #asWeiValue(#resolveExpr(EXPR), UNIT)

    rule #resolveExpr(%num256_add(LEFTE, RIGHTE)) => #num256Add(#resolveExpr(LEFTE), #resolveExpr(RIGHTE))

    rule #resolveExpr(%num256_sub(LEFTE, RIGHTE)) => #num256Sub(#resolveExpr(LEFTE), #resolveExpr(RIGHTE))


    syntax CTypedLLLExp ::= "#asNum128"    "(" CTypedLLLExp ")"    [strict]
    syntax CTypedLLLExp ::= "#asNum128Aux" "(" LLLExp ")"
 // -----------------------------------------------------------------------
    rule #asNum128(@tlll(T, CODE))
             => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %num256) orBool #isTypeOf(T, %address),
                            #asNum128Aux(CODE),
                            #exception("Function arg type does not match expected type."))

    rule #asNum128Aux(CODE) => @tlll(%num, $clamp($mload(#minNumPos), CODE, $mload(#maxNumPos)))


    syntax CTypedLLLExp ::= "#asNum256"    "(" CTypedLLLExp ")"    [strict]
    syntax CTypedLLLExp ::= "#asNum256Aux" "(" TypedLLLExp ")"
    syntax CTypedLLLExp ::= "#asNum256ForNumber" "(" LLLExp ")"
    syntax CTypedLLLExp ::= "#asNum256ForLLLExp" "(" LLLExp ")"
 // -----------------------------------------------------------------------
    rule #asNum256(@tlll(T, CODE))
             => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %bytes32) orBool #isTypeOf(T, %address),
                            #asNum256Aux(@tlll(T, CODE)),
                            #exception("Function arg type does not match expected type."))

    rule #asNum256Aux(@tlll(T, CODE)) => #ifThenElse(isInt(CODE),
                                                     #asNum256ForNumber(CODE),
                                                     #asNum256ForLLLExp(CODE))

    rule #asNum256ForNumber(I:Int) => #ifThenElse((I >=Int 0) andBool (I <=Int 2^Int 256 -Int 1),
                                                   @tlll(%num256, I),
                                                   #exception("Number out of range"))

    rule #asNum256ForLLLExp(CODE) => @tlll(%num256, CODE)


    syntax CTypedLLLExp ::= "#asWeiValue"    "(" CTypedLLLExp "," Id  ")"                [strict(1)]
    syntax CTypedLLLExp ::= "#asWeiValueAux" "(" TypedLLLExp  "," Int ")"
    syntax CTypedLLLExp ::= "#asWeiValueForNumber" "(" LLLExp      "," Int ")"
    syntax CTypedLLLExp ::= "#asWeiValueForLLLExp" "(" TypedLLLExp "," Int ")"
 // ------------------------------------------------------------------------------------------------
    rule #asWeiValue(@tlll(T, CODE), UNIT)
             => #ifThenElse(#isTypeOf(T, %num) orBool #isTypeOf(T, %decimal),
                            #asWeiValueAux(@tlll(T, CODE), #convertToWei(UNIT)),
                            #exception("Function arg type does not match expected type."))

    rule #asWeiValueAux(@tlll(T, CODE), DENOMINATION)
             => #ifThenElse(isInt(CODE),
                            #asWeiValueForNumber(CODE, DENOMINATION),
                            #asWeiValueForLLLExp(@tlll(T, CODE), DENOMINATION))

    rule #asWeiValueForLLLExp(@tlll(%num, CODE), DENOMINATION) => @tlll(%unit(%num, %wei, false), $mul(CODE, DENOMINATION))

    rule #asWeiValueForLLLExp(@tlll(%decimal, CODE), DENOMINATION)
             => @tlll(%unit(%num, %wei, false), $div($mul(CODE, DENOMINATION), #decimalDivisor))


    syntax CTypedLLLExp ::= "#num256Add"    "(" CTypedLLLExp "," CTypedLLLExp ")"        [seqstrict]
    syntax CTypedLLLExp ::= "#num256AddAux" "(" LLLExp "," LLLExp ")"
 // ------------------------------------------------------------------------------------------------
    rule #num256Add(@tlll(LT, LCODE), @tlll(RT, RCODE))
            => #ifThenElse(#isTypeOf(LT, %num256) andBool #isTypeOf(RT, %num256),
                           #num256AddAux(LCODE, RCODE),
                           #exception("Function arg type does not match expected type."))

    rule #num256AddAux(LCODE, RCODE)
             => @tlll(%num256, $%seq(
                                 $assert($or($iszero(RCODE), $gt($add(LCODE, RCODE), LCODE)));
                                 $add(LCODE, RCODE);.LLLExps))


    syntax CTypedLLLExp ::= "#num256Sub"    "(" CTypedLLLExp "," CTypedLLLExp ")"        [seqstrict]
    syntax CTypedLLLExp ::= "#num256SubAux" "(" LLLExp "," LLLExp ")"
 // ------------------------------------------------------------------------------------------------
    rule #num256Sub(@tlll(LT, LCODE), @tlll(RT, RCODE))
            => #ifThenElse(#isTypeOf(LT, %num256) andBool #isTypeOf(RT, %num256),
                           #num256SubAux(LCODE, RCODE),
                           #exception("Function arg type does not match expected type."))

    rule #num256SubAux(LCODE, RCODE)
             => @tlll(%num256, $%seq(
                                 $assert($ge(LCODE, RCODE));
                                 $sub(LCODE, RCODE);.LLLExps))


    // Arithmetic
    syntax CTypedLLLExp ::= "#binOp"    "(" BinOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
    syntax CTypedLLLExp ::= "#binOpAux" "(" BinOp "," TypedLLLExp "," TypedLLLExp ")"
 // -----------------------------------------------------------------------------------------------------
    rule #resolveExpr(%binop(BOP, LEFTE, RIGHTE)) => #binOp(BOP, #resolveExpr(LEFTE), #resolveExpr(RIGHTE))

    rule #binOp(BOP, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
                        #exception("Unsupported types for arithmetic op"))
             ~> #clampArithResult(#binOpAux(BOP, @tlll(LT, LCODE), @tlll(RT, RCODE)))

    rule #binOpAux(+, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThenElse(LT ==K RT,
                            @tlll(LT, $add(LCODE, RCODE)),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%decimal, $add($mul(LCODE, #decimalDivisor), RCODE)),
                    #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                                @tlll(%decimal, $add(LCODE, $mul(RCODE, #decimalDivisor))),
                                #exception("How did I get here?"))))

    rule #binOpAux(-, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThenElse(LT ==K RT,
                            @tlll(LT, $sub(LCODE, RCODE)),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%decimal, $sub($mul(LCODE, #decimalDivisor), RCODE)),
                    #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                                @tlll(%decimal, $sub(LCODE, $mul(RCODE, #decimalDivisor))),
                                #exception("How did I get here?"))))

    // Compare
    syntax CTypedLLLExp ::= "#compareOp"    "(" CompareOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
    syntax CTypedLLLExp ::= "#compareOpAux" "(" CompareOp "," TypedLLLExp "," TypedLLLExp ")"
 // -------------------------------------------------------------------------------------------------------------
    rule #resolveExpr(%compareop(COP, LEFTE, RIGHTE)) => #compareOp(COP, #resolveExpr(LEFTE), #resolveExpr(RIGHTE))

    rule #compareOp(COP, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThen(notBool(isNumericType(LT)) orBool notBool(isNumericType(RT)),
                #ifThen(COP =/=K %eq andBool COP =/=K %ne,
                        #exception("Invalid type for comparison op")))
           ~> #compareOpAux(COP, @tlll(LT, LCODE), @tlll(RT, RCODE))

    rule #compareOpAux(%gt, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $sgt(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $sgt(LCODE, $mul(RCODE, #decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $sgt($mul(LCODE, #decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%ge, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $sge(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $sge(LCODE, $mul(RCODE, #decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $sge($mul(LCODE, #decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%lt, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $slt(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $slt(LCODE, $mul(RCODE, #decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $slt($mul(LCODE, #decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%le, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $sle(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $sle(LCODE, $mul(RCODE, #decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $sle($mul(LCODE, #decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%eq, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $eq(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $eq(LCODE, $mul(RCODE, #decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $eq($mul(LCODE, #decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))

    rule #compareOpAux(%ne, @tlll(LT, LCODE), @tlll(RT, RCODE))
           => #ifThenElse(LT ==K RT,
                          @tlll(%bool, $ne(LCODE, RCODE)),
                #ifThenElse(LT ==K %decimal andBool RT ==K %num,
                            @tlll(%bool, $ne(LCODE, $mul(RCODE, #decimalDivisor))),
                  #ifThenElse(LT ==K %num andBool RT ==K %decimal,
                              @tlll(%bool, $ne($mul(LCODE, #decimalDivisor), RCODE)),
                              #exception("Unsupported types for comparison"))))


    // Bool
    syntax CTypedLLLExp ::= "#boolOp" "(" BoolOp "," CTypedLLLExp "," CTypedLLLExp ")"  [seqstrict(2,3)]
    syntax CTypedLLLExp ::= "#boolOpAux" "(" BoolOp "," TypedLLLExp "," TypedLLLExp ")"
 // ----------------------------------------------------------------------------------------------------
    rule #resolveExpr(%boolop(BOP, LEFTE, RIGHTE)) => #boolOp(BOP, #resolveExpr(LEFTE), #resolveExpr(RIGHTE))

    rule #boolOp(BOP, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => #ifThenElse((LT ==K %bool) andBool (RT ==K %bool),
                            #boolOpAux(BOP, @tlll(LT, LCODE), @tlll(RT, RCODE)),
                            #exception("Boolean operations can only be between booleans!"))

    rule #boolOpAux(%and, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => @tlll(%bool, $and(LCODE, RCODE))

    rule #boolOpAux(%or, @tlll(LT, LCODE), @tlll(RT, RCODE))
             => @tlll(%bool, $or(LCODE, RCODE))


    // Unary
    syntax CTypedLLLExp ::= "#unaryOp" "(" UnaryOp "," CTypedLLLExp ")"    [strict(2)]
 // ----------------------------------------------------------------------------------
    rule #resolveExpr(%unaryop(UOP, EXPR)) => #unaryOp(UOP, #resolveExpr(EXPR))

    rule #unaryOp(%not, @tlll(T, CODE)) => @tlll(%bool, $iszero(CODE))

    rule #unaryOp(%neg, @tlll(T, CODE)) => #ifThenElse(isNumericType(T),
                                                       @tlll(T, $sub(0, CODE)),
                                                       #exception("Unsupported type for negation."))


    syntax CTypedLLLExp ::= "#clampArithResult" "(" CTypedLLLExp ")"                     [strict]
 // ---------------------------------------------------------------------------------------------
    rule #clampArithResult(@tlll(%num, CODE))
              => @tlll(%num, $clamp($mload(#minNumPos), CODE, $mload(#maxNumPos)))

    rule #clampArithResult(@tlll(%decimal, CODE))
              => @tlll(%decimal, $clamp($mload(#minDecimalPos), CODE, $mload(#maxDecimalPos)))


    syntax CTypedLLLExp ::= "#unwrapLocation" "(" CTypedAddr ")"  [strict]
 // ----------------------------------------------------------------------
    rule #unwrapLocation(@taddr(T, LOC, false, _)) => @tlll(T, $mload(LOC))
    rule #unwrapLocation(@taddr(T, LOC, true, _)) => @tlll(T, $sload(LOC))
   

    syntax CLLLExps    ::= "#convertToLLLExps" "(" CLLLExp ")"    [strict]
 // ----------------------------------------------------------------------
    rule #convertToLLLExps(CODE) => CODE;.LLLExps


    syntax KItem       ::= "#cleanConfig"
 // -------------------------------------
    rule <k> CODE:LLLExps ~> (#cleanConfig => .) ...</k>
         <env> _ => .Map </env>
         <nextMem> _ => #reservedMemPos </nextMem>
         <forvar> _ => .Set </forvar>
         <return> _ => %void </return>
         <constant> _ => false </constant>
         <payable> _ => false </payable>                       [structural]


    syntax KItem       ::= "#exception" "(" String ")"
 // --------------------------------------------------


 //////////////////////////////////////////////////////////////////////////////
 // Utils
 //////////////////////////////////////////////////////////////////////////////


    syntax Bool ::= "#isInitFunc" "(" Id ")"    [function]
 // ------------------------------------------------------
    rule #isInitFunc(NAME) => NAME ==K __init__


    syntax Map  ::= "#updateEnv" "(" Var "," Type "," Int "," Map "," Bool /*mutable*/ ")"   [function]
    syntax Map  ::= "#flattenStruct" "(" Var "," VarDecls "," Int "," Map "," Bool ")"       [function]
 // ---------------------------------------------------------------------------------------------------
    rule #updateEnv(V, %struct(VARDECLS), LOC, M, ISMUTABLE) => #flattenStruct(V, VARDECLS, LOC, M, ISMUTABLE)

    rule #updateEnv(V, T, LOC, M, ISMUTABLE) => M[V <- @taddr(T, LOC, false, ISMUTABLE)]    requires notBool isStructType(T)

    rule #flattenStruct(V, .VarDecls, LOC, M, ISMUTABLE) => M

    rule #flattenStruct(V, %vdecl(NAME, T) VS, LOC, M, ISMUTABLE)
             => #flattenStruct(V, VS, LOC +Int #sizeOfType(T), #updateEnv(%mem(V, NAME), T, LOC, M, ISMUTABLE), ISMUTABLE)


    syntax Int       ::= "#sizeOfParams" "(" Params ")"   [function]
    syntax Int       ::= "#sizeOfParam"  "(" Param  ")"   [function]
 // --------------------------------------------------------------
    rule #sizeOfParams(.Params) => 0

    rule #sizeOfParams(P PS)    => #sizeOfParam(P) +Int #sizeOfParams(PS)

    rule #sizeOfParam(%param(_, %bytes(_))) => 32

    rule #sizeOfParam(%param(_, T)) => #sizeOfType(T)    requires notBool isByteArrayType(T)


    syntax Int      ::= "#sizeOfStmts" "(" Stmts ")"    [function]
 // --------------------------------------------------------------
    rule #sizeOfStmts(.Stmts) => 0

    rule #sizeOfStmts(STMT STMTS) => 1 +Int #sizeOfStmts(STMTS)


    syntax Int       ::= "#sizeOfType" "(" Type ")"     [function]
 // --------------------------------------------------------------
    rule #sizeOfType(T:BaseType) => 32

    rule #sizeOfType(%bytes(L)) => #ceil32(L) +Int 64

    rule #sizeOfType(%list(T, N)) => #sizeOfType(T) *Int N

    rule #sizeOfType(%struct(.VarDecls)) => 0

    rule #sizeOfType(%struct(%vdecl(_, T) VS)) => #sizeOfType(T) +Int #sizeOfType(%struct(VS))


    syntax Int       ::= "#ceil32" "(" Int ")"     [function]
 // ---------------------------------------------------------
    rule #ceil32(I) => I +Int 31 -Int (I -Int 1) %Int 32


    syntax String    ::= "#canonicalizeType" "(" Type ")"  [function]
 // -----------------------------------------------------------------
    rule #canonicalizeType(%bytes(L)) => "bytes"

    rule #canonicalizeType(%list(T, N)) => #canonicalizeType(T) +String "[" +String Int2String(N) +String "]"
         requires isBaseType(T)

    rule #canonicalizeType(%num) => "int128"

    rule #canonicalizeType(%decimal) => "decimal10"

    rule #canonicalizeType(%num256) => "uint256"
   
    rule #canonicalizeType(%bool) => "bool"
 
    rule #canonicalizeType(%address) => "address"
 
    rule #canonicalizeType(%bytes32) => "bytes32"


    syntax Bool     ::= "#isTypeOf" "(" Type "," Type /*target type*/ ")"    [function]
 // ------------------------------------------------------------------------------------
    rule #isTypeOf(T, TARGET) => #isUnitTypeOf(T, TARGET)
      requires isUnitType(T)

    rule #isTypeOf(T, TARGET) => T ==K TARGET
      requires notBool isUnitType(T)


    syntax Bool     ::= "#isUnitTypeOf" "(" UnitType "," Type ")"       [function]
 // ------------------------------------------------------------------------------
    rule #isUnitTypeOf(%unit(T, _, _), T) => true

    rule #isUnitTypeOf(%unit(T, _, _), TARGET) => false
      requires T =/=K TARGET


    syntax Bool      ::= "#inDecorators" "(" Decorator "," Decorators ")"      [function]
 // -------------------------------------------------------------------------------------
    rule #inDecorators(D, .Decorators) => false

    rule #inDecorators(D, DEC DECS) => true                     requires D ==K DEC

    rule #inDecorators(D, DEC DECS) => #inDecorators(D, DECS)   requires D =/=K DEC


    syntax String   ::= "#generateSignature" "(" String "," Params ")"  [function]
 // ------------------------------------------------------------------------------
    rule #generateSignature(SIGN, %param(_,T) PARAM1 PARAMS) 
             => #generateSignature(SIGN +String #canonicalizeType(T) +String "," , PARAM1 PARAMS)
    
    rule #generateSignature(SIGN, %param(_,T) .Params) 
             => #generateSignature(SIGN +String #canonicalizeType(T), .Params)

    rule #generateSignature(SIGN, .Params) => SIGN +String ")"


    syntax Int     ::= "#generateMethodId" "(" Id "," Params ")"       [function]
 // ------------------------------------------------------------------------------
    rule #generateMethodId(__init__, PARAMS) => 0

    rule #generateMethodId(NAME, PARAMS)
             => String2Base(substrString(Keccak256(#generateSignature(Id2String(NAME) +String "(", PARAMS)), 0, 8), 16)
      requires NAME =/=K __init__


    syntax LLLExps  ::= List{LLLExp, ";"}
    syntax LLLExp   ::= "$%seq" "(" LLLExps ")"
    syntax LLLExps  ::= LLLExps "++LLL" LLLExps      [left, function]
 // -----------------------------------------------------------------
    rule .LLLExps    ++LLL LES:LLLExps => LES

    rule (LE ; LES1) ++LLL LES2        => LE ; (LES1 ++LLL LES2)


    syntax LLLExps  ::= "#mkClamper"        "(" Type "," Int /*data pos*/ "," Int /*mem pos*/ "," Bool ")"    [function]
    syntax LLLExps  ::= "#mkClamperForList" "(" Int /*length*/ "," Type "," Int "," Int "," Bool ")"          [function]
    syntax LLLExp   ::= "#mkCopier"         "(" LLLExp "," LLLExp "," LLLExp "," Bool ")"                     [function]
    syntax LLLExp   ::= "#mkDataDecl"       "(" LLLExp "," Bool ")"                                           [function]
 // --------------------------------------------------------------------------------------------------------------------
    rule #mkClamper(%num     , DPOS, MPOS, ISINIT) => $clamp(
                                                        $mload(#minNumPos),
                                                        #mkDataDecl(DPOS, ISINIT),
                                                        $mload(#maxNumPos)
                                                      );.LLLExps

    rule #mkClamper(%num256  , _, _, _ ) => $pass;.LLLExps

    rule #mkClamper(%bool    , DPOS, MPOS, ISINIT) => $uclamplt(#mkDataDecl(DPOS, ISINIT), 2);.LLLExps

    rule #mkClamper(%address , DPOS, MPOS, ISINIT) => $uclamplt(#mkDataDecl(DPOS, ISINIT), $mload(#addrSizePos));.LLLExps

    rule #mkClamper(%bytes(L), DPOS, MPOS, ISINIT)
             => $%seq(
                  #mkCopier(MPOS, #mkDataDecl(DPOS, ISINIT), 32 +Int L, ISINIT);
                  $assert(
                    $le(
                      $calldataload($add(4, #mkDataDecl(DPOS, ISINIT))),
                      L
                    )
                  )
                );.LLLExps

    rule #mkClamper(%list(T, N), DPOS, MPOS, ISINIT) => $%seq(#mkClamperForList(N, T, DPOS, MPOS, ISINIT));.LLLExps

    rule #mkClamperForList(0, T, DPOS, MPOS, ISINIT) => .LLLExps

    rule #mkClamperForList(N, T, DPOS, MPOS, ISINIT)
             => #mkClamper(T, DPOS, MPOS, ISINIT) ++LLL
                #mkClamperForList(N -Int 1, T, DPOS +Int #sizeOfType(T), MPOS +Int #sizeOfType(T), ISINIT)

    rule #mkCopier(MPOS, POS, SZ, true) => $codecopy(MPOS, $add($codelen, POS), SZ)

    rule #mkCopier(MPOS, POS, SZ, false) => $calldatacopy(MPOS, $add(4, POS), SZ)

    rule #mkDataDecl(DATAPOS, true) => $codeload($add($codelen, DATAPOS))

    rule #mkDataDecl(DATAPOS, false) => $calldataload($add(4, DATAPOS))


    syntax LLLExps  ::= "#initializer_lll"      [function]
 // ------------------------------------------------------
    rule #initializer_lll => $%seq(
                               $mstore(28 , $calldataload(0));
                               $mstore(#addrSizePos , 2 ^Int 160);
                               $mstore(#maxNumPos , 2 ^Int 127 -Int 1);
                               $mstore(#minNumPos , -2 ^Int 127);
                               $mstore(#maxDecimalPos, (2 ^Int 127 -Int 1) *Int 10000000000);
                               $mstore(#minDecimalPos, (-2 ^Int 127) *Int 10000000000)
                             );.LLLExps


    syntax Int    ::= "#convertToWei" "(" Id ")"    [function]
 // ----------------------------------------------------------
    rule #convertToWei(wei)      => 1

    rule #convertToWei(kwei)     => 10 ^Int 3

    rule #convertToWei(ada)      => 10 ^Int 3

    rule #convertToWei(lovelace) => 10 ^Int 3

    rule #convertToWei(babbage)  => 10 ^Int 6

    rule #convertToWei(shannon)  => 10 ^Int 9

    rule #convertToWei(gwei)     => 10 ^Int 9

    rule #convertToWei(szabo)    => 10 ^Int 12

    rule #convertToWei(finney)   => 10 ^Int 15

    rule #convertToWei(ether)    => 10 ^Int 18


    syntax KItem  ::= "#ifThen" "(" Bool /*condition*/ "," K /*then*/ ")"
 // ---------------------------------------------------------------------
    rule #ifThen(true, THENCLAUSE) => THENCLAUSE
    rule #ifThen(false, THENCLAUSE) => .


    syntax KItem  ::= "#ifThenElse" "(" Bool /*condition*/ "," K /*then*/ "," K /*else*/ ")"
 // ----------------------------------------------------------------------------------------
    rule #ifThenElse(true, THENCLAUSE, ELSECLAUSE) => THENCLAUSE
    rule #ifThenElse(false, THENCLAUSE, ELSECLAUSE) => ELSECLAUSE


    syntax Defs   ::= "#mkPublicGetters" "(" Globals "," Defs ")"    [function]
    syntax Defs   ::= "#mkPublicGetter" "(" Id "," Type ")"          [function]
 // ---------------------------------------------------------------------------
    rule #mkPublicGetters(.Globals, DEFS) => DEFS

    rule #mkPublicGetters(%svdecl(NAME, T, %public) GS, DEFS)
           => #mkPublicGetters(GS, DEFS ++Def #mkPublicGetter(NAME, T))

    rule #mkPublicGetters(%svdecl(_, _, %private) GS, DEFS)
           => #mkPublicGetters(GS, DEFS)

    rule #mkPublicGetter(NAME, T)
           => %fdecl(%@constant .Decorators,
                     String2Id("get_" +String Id2String(NAME)),
                     .Params,
                     T,
                     %return(%svar(NAME)) .Stmts) .Defs
      requires isBaseType(T)


    syntax Defs   ::= Defs "++Def" Defs                    [function]
 // -----------------------------------------------------------------
    rule .Defs ++Def DEFS:Defs => DEFS

    rule (DEF DEFS1) ++Def DEFS2:Defs => DEF (DEFS1 ++Def DEFS2)


endmodule
