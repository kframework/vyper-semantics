
@public
def foo(inp: bytes <= 10) -> bytes <= 3:
    return slice(inp, start=block.timestamp, len=3)
    