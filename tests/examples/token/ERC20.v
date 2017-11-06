%pgm(
  %svdecl(balance, %map(%num256, %address), %private)
  %svdecl(allowances, %map(%map(%num256, %address), %address), %private)
  %svdecl(num_issued, %num256, %private),
  %fdecl(%@payable, deposit, ,%void,
    %assign(%var(_value), %as_num256(%msg.value))
    %assign(%var(_sender), %msg.sender)
    %assign(%mapelem(%svar(balance), %var(_sender)), %num256_add(%mapelem(%svar(balance), %var(_sender)), %var(_value)))
    %assign(%svar(num_issued), %num256_add(%svar(num_issued), %var(_value)))
  )
)

