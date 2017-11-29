
@public
def foo(inp: bytes <= 100) -> bytes32:
    return sha3(inp)

@public
def bar() -> bytes32:
    return sha3("inp")
    