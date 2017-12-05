MyLog: __log__({arg1: indexed(bytes <= 3), arg2: indexed(bytes <= 4), arg3: indexed(address)})

@public
def foo():
    log.MyLog('bar', 'home', self)
