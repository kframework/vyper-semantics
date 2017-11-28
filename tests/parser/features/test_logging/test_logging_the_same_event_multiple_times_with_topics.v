%pgm(
  %event(MyLog, %eparam(arg1, %num, true) %eparam(arg2, %address, true)), ,
  %fdecl(%@public, foo, , %void,
    %log(MyLog, 1 %self)
    %log(MyLog, 1 %self))
  %fdecl(%@public, bar, , %void,
    %log(MyLog, 1 %self)
    %log(MyLog, 1 %self))
)
