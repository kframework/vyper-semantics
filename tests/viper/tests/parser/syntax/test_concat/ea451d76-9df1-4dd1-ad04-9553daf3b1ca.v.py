
@public
def sandwich(inp: bytes <= 100, inp2: bytes32) -> bytes <= 165:
    return concat(inp2, inp, inp2)
    