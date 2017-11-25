%pgm(, ,
  %fdecl(%@public, foo, , %void,
    %assign(%var(x), %list(1, 2, 3))
    %assign(%var(x), %list(4, 5, 6))
    %assign(%var(y), %var(x)))
)
