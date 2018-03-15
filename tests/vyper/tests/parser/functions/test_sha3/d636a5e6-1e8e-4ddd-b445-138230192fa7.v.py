
@public
def foo(inp: bytes <= 100) -> bool:
    return sha3(inp) == sha3("badminton")
    