
@public
def foo(inp: bytes <= 32) -> num:
    return extract32(inp, 0, type=num128)

@public
def bar(inp: bytes <= 32) -> num256:
    return extract32(inp, 0, type=num256)

@public
def baz(inp: bytes <= 32) -> bytes32:
    return extract32(inp, 0, type=bytes32)

@public
def fop(inp: bytes <= 32) -> bytes32:
    return extract32(inp, 0)

@public
def foq(inp: bytes <= 32) -> address:
    return extract32(inp, 0, type=address)
    