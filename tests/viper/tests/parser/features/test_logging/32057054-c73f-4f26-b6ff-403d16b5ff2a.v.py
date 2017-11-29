
MyLog: __log__({arg1: indexed(num), arg2: bytes <= 3})
YourLog: __log__({arg1: indexed(address), arg2: bytes <= 5})

@public
def foo():
    log.MyLog(1, 'bar')
    log.YourLog(self, 'house')
    