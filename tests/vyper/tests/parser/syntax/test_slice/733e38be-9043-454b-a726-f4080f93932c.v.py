
@public
def foo(inp: bytes <= 10) -> bytes <= 4:
    return slice(inp, start=2, len=3)
    