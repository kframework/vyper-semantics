%pgm(
  %event(Transfer, %eparam(_from, %address, true) %eparam(_to, %address, true) %eparam(_value, %num256, false))
  %event(Approval, %eparam(_owner, %address, true) %eparam(_spender, %address, true) %eparam(_value, %num256, false)),
  %svdecl(balances, %mapT(%num256, %address), %private)
  %svdecl(allowances, %mapT(%mapT(%num256, %address), %address), %private)
  %svdecl(num_issued, %num256, %private),
  %fdecl(%@payable, deposit, ,%void,
    %assign(%var(_value), %as_num256(%msg.value))
    %assign(%var(_sender), %msg.sender)
    %assign(%mapelem(%svar(balances), %var(_sender)), %num256_add(%mapelem(%svar(balances), %var(_sender)), %var(_value)))
    %assign(%svar(num_issued), %num256_add(%svar(num_issued), %var(_value)))
    %log(Transfer, %hex("0000000000000000000000000000000000000000"), %var(_sender), %var(_value))
  )
  %fdecl(, withdraw, %param(_value, %num256) , %bool,
    %assign(%var(_sender), %msg.sender)
    %assign(%mapelem(%svar(balances), %var(_sender)), %num256_sub(%mapelem(%svar(balances), %var(_sender)), %var(_value)))
    %assign(%svar(num_issued), %num256_sub(%svar(num_issued), %var(_value)))
    %send(%var(_sender), %as_wei_value(%as_num128(%var(_value)), wei))
    %log(Transfer, %var(_sender), %hex("0000000000000000000000000000000000000000"), %var(_value))
    %return(true)
  )
  %fdecl(%@constant, totalSupply, , %num256,
    %return(%svar(num_issued))
  )
  %fdecl(%@constant, balanceOf, %param(_owner, %address), %num256,
    %return(%mapelem(%svar(balances), %var(_owner)))
  )
  %fdecl(, transfer, %param(_to, %address) %param(_value, %num256), %bool,
    %assign(%var(_sender), %msg.sender)
    %assign(%mapelem(%svar(balances), %var(_sender)), %num256_sub(%mapelem(%svar(balances), %var(_sender)), %var(_value)))
    %assign(%mapelem(%svar(balances), %var(_to)), %num256_add(%mapelem(%svar(balances), %var(_to)), %var(_value)))
    %log(Transfer, %var(_sender), %var(_to), %var(_value))
    %return(true)
  )
  %fdecl(, transferFrom, %param(_from, %address) %param(_to, %address) %param(_value, %num256), %bool,
    %assign(%var(_sender), %msg.sender)
    %assign(%var(allowance), %mapelem(%mapelem(%svar(allowances), %var(_from)), %var(_sender)))
    %assign(%mapelem(%svar(balances), %var(_from)), %num256_sub(%mapelem(%svar(balances), %var(_from)), %var(_value)))
    %assign(%mapelem(%svar(balances), %var(_to)), %num256_add(%mapelem(%svar(balances), %var(_to)), %var(_value)))
    %assign(%mapelem(%mapelem(%svar(allowances), %var(_from)), %var(_sender)),
            %num256_sub(%var(allowance), %var(_value)))
    %log(Transfer, %var(_from), %var(_to), %var(_value))
    %return(true)
  )
  %fdecl(, approve, %param(_spender, %address) %param(_value, %num256), %bool,
    %assign(%var(_sender), %msg.sender)
    %assign(%mapelem(%mapelem(%svar(allowances), %var(_sender)), %var(_spender)), %var(_value))
    %log(Approval, %var(_sender), %var(_spender), %var(_value))
    %return(true)
  )
  %fdecl(%@constant, allowance, %param(_owner, %address) %param(_spender, %address), %num256,
    %return(%mapelem(%mapelem(%svar(allowances), %var(_owner)), %var(_spender)))
  )
)

