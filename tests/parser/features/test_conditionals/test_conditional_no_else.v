%pgm(, ,
  %fdecl(%@public, foo, %param(i, %bool), %num,
    %if(%var(i),
      %return(5),)
    %return(11))
)
