
class Foo():
    def set_lucky(_lucky: num) -> num: pass

@public
@constant
def set_lucky_expr(arg1: address, arg2: num):
    Foo(arg1).set_lucky(arg2)

@public
@constant
def set_lucky_stmt(arg1: address, arg2: num) -> num:
    return Foo(arg1).set_lucky(arg2)
    