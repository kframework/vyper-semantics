
@public
def foo(inp: bytes <= 50) -> bytes <= 1000:
    x = inp
    return concat(x, inp, x, inp, x, inp, x, inp, x, inp)
    