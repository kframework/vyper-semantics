
g: {a: bytes <= 50, b: bytes <= 50}

@public
def foo(inp1: bytes <= 40, inp2: bytes <= 45):
    self.g = {a: inp1, b: inp2}

@public
def check1() -> bytes <= 50:
    return self.g.a

@public
def check2() -> bytes <= 50:
    return self.g.b

@public
def bar(inp1: bytes <= 40, inp2: bytes <= 45) -> bytes <= 50:
    h = {a: inp1, b: inp2}
    return h.a

@public
def bat(inp1: bytes <= 40, inp2: bytes <= 45) -> bytes <= 50:
    h = {a: inp1, b: inp2}
    return h.b

@public
def quz(inp1: bytes <= 40, inp2: bytes <= 45):
    h = {a: inp1, b: inp2}
    self.g = h
    