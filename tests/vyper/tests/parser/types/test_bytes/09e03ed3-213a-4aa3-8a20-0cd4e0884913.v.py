
a: bytes <= 60
@public
def foo(inp: bytes <= 60) -> bytes <= 60:
    self.a = inp
    self.a = None
    return self.a

@public
def bar(inp: bytes <= 60) -> bytes <= 60:
    b = inp
    b = None
    return b
    