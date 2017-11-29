
MyLog: __log__({arg1: indexed(bytes <= 4), arg2: indexed(bytes <= 29), arg3: bytes<=31})

@public
def foo(arg1: bytes <= 29, arg2: bytes <= 31):
    log.MyLog('bar', arg1, arg2)
