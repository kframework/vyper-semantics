module BALANCEOF-SPEC
  imports VIPER

  rule
    <k> (#call(ACCTFROM, ACCTTO, 0, balanceOf, @ee(%address, OWNER:Int, true)) => @ee(%num256, BAL, false))</k>

    <vyper>

      <callStack>     CALLSTACK     </callStack>
      <interimStates> INTERIMSTACK  </interimStates>
      <substateStack> SUBSTATESTACK </substateStack>

      <memory>   MEM      </memory>
      <memStack> MEMSTACK </memStack>  // for block scoping
      <forLoop>
        <forvar> FORVAR  </forvar>  // Variables defined in for loops, eg. for i in range(6):...
        <inLoop> INLOOP  </inLoop>  // In Loop status. Whether body is currently evaluating within a for-loop or not.
      </forLoop>
      <constant> CONSTANT </constant>  // Is the current function constant?
      <return>   RETURN   </return>
      <order>    -1       </order>

      // transaction
      <id>        ACCTID    </id>
      <caller>    CALLER    </caller>
      <callValue> CALLVALUE </callValue>

      // execution substate
      <substate>
        <selfDestruct> SELFDESTRUCT  </selfDestruct>
        <log>          LOG           </log>
      </substate>

    </vyper>

    // Ethereum Network
    // ================

    <network>
      <activeAccounts> SetItem(ACCTFROM) SetItem(ACCTTO) </activeAccounts>
      <accounts>
        <account>
          <acctID>   ACCTTO    </acctID>
          <balance>  TOBAL     </balance>
          <fun>  balanceOf |-> @func(balanceOf, %param(_owner, %address) .Params, %num256, %return(%subscript(%svar(balances), %var(_owner))) .Stmts, true, false, false, 3) </fun>
          <event> .Map </event>
          <external> .Map </external>
          <storage>  balances |-> @val(@tv(%mapT(%address,%num256), OWNER |-> @tv(%num256, BAL) _:Map), true) </storage>
        </account>
        <account>
          <acctID> ACCTFROM </acctID>
          <balance> FROMBAL </balance>
          <fun> _ </fun>
          <event> _ </event>
          <external> _ </external>
          <storage> _ </storage>
        </account>
      </accounts>
    </network>
    requires ACCTFROM =/=K ACCTTO andBool FROMBAL >=Int 0

endmodule

