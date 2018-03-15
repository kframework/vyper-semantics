%pgm(, ,
  %fdecl(%@public, augadd, %param(x, %num) %param(y, %num), %num,
    %assign(%var(z), %var(x))
    %augassign(+=, %var(z), %var(y))
    %return(%var(z)))
  %fdecl(%@public, augmul, %param(x, %num) %param(y, %num), %num,
    %assign(%var(z), %var(x))
    %augassign(*=, %var(z), %var(y))
    %return(%var(z)))
  %fdecl(%@public, augsub, %param(x, %num) %param(y, %num), %num,
    %assign(%var(z), %var(x))
    %augassign(-=, %var(z), %var(y))
    %return(%var(z)))
  %fdecl(%@public, augdiv, %param(x, %num) %param(y, %num), %num,
    %assign(%var(z), %var(x))
    %augassign(/=, %var(z), %var(y))
    %return(%var(z)))
  %fdecl(%@public, augmod, %param(x, %num) %param(y, %num), %num,
    %assign(%var(z), %var(x))
    %augassign(%=, %var(z), %var(y))
    %return(%var(z)))
)

