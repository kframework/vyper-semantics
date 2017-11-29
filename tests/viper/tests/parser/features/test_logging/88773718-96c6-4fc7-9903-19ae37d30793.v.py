
MyLog: __log__({arg1: num[2], arg2: timestamp[3], arg3: num[2][2]})

@public
def foo():
    log.MyLog([1,2], [block.timestamp, block.timestamp+1, block.timestamp+2], [[1,2],[1,2]])
    log.MyLog([1,2], [block.timestamp, block.timestamp+1, block.timestamp+2], [[1,2],[1,2]])
    