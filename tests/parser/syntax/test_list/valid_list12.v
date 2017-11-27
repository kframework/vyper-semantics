%pgm(,
  %svdecl(foo, %listT(%num, 3), %private),
  %fdecl(%@public, foo, , %void,
    %assign(%svar(foo), %list(1 2 3)))
)
