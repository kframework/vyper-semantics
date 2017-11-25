%pgm(,
  %svdecl(foo, %listT(%decimal, 3), %private),
  %fdecl(%@public, foo, , %void,
    %assign(%svar(foo), %list(1, %fixed10(21, 10), 3)))
)
