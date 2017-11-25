%pgm(, ,
  %fdecl(%@public, foo, , %listT(%listT(%decimal, 2), 2),
    %return(%list(%list(1, %fixed10(20, 10)), %list(%fixed10(35, 10), 4))))
)
