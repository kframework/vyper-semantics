@public
def foo() -> num:
    return 3

@public
def bar() -> num:
    return self.foo()
