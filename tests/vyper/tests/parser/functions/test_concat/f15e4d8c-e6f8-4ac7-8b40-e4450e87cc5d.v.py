
ecks: bytes32

@public
def foo(x: bytes32, y: bytes32) -> bytes <= 64:
    selfecks = x
    return concat(selfecks, y)

@public
def goo(x: bytes32, y: bytes32) -> bytes <= 64:
    self.ecks = x
    return concat(self.ecks, y)

@public
def hoo(x: bytes32, y: bytes32) -> bytes <= 64:
    return concat(x, y)
    