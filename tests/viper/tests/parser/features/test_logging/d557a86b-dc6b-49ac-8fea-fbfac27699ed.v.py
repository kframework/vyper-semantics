
MyLog: __log__({arg1: indexed(num), arg2: indexed(address)})

@public
def foo():
    log.MyLog(1, self)
    log.MyLog(1, self)

@public
def bar():
    log.MyLog(1, self)
    log.MyLog(1, self)
    