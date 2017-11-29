
class Foo():
        def foo(arg1: num) -> num: pass

@public
def bar(arg1: address, arg2: num) -> num:
    return Foo(arg1).foo(arg2)
    