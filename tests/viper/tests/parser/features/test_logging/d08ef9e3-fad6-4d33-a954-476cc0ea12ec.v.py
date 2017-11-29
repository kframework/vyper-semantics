
MyLog: __log__({arg1: indexed(num), arg2: bytes <= 3})

@public
def foo():
    log.MyLog(1, 'bar')
    