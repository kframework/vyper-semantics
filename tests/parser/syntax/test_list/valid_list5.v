%pgm(, ,
  %fdecl(%@public, foo, %param(x, %listT(%num, 3)), %num,
    %return(%listelem(%var(x), 0)))
)
