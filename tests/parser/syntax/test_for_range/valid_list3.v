%pgm(, ,
  %fdecl(%@public, foo, , %void,
    %assign(%var(x), 5)
    %forrange(i, %var(x), %binop(+, %var(x), 10),
      %pass))
)
