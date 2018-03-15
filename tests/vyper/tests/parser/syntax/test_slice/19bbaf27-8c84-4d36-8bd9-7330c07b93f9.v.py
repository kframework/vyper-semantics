
@public
def foo(inp: bytes <= 10) -> bytes <= 3:
    return slice(inp, start=4.0, len=3)
    