
test: bytes <= 100

@public
def set_test(inp: bytes <= 100):
    self.test = inp

@public
def tryy(inp: bytes <= 100) -> bool:
    return sha3(inp) == sha3(self.test)

@public
def trymem(inp: bytes <= 100) -> bool:
    x = self.test
    return sha3(inp) == sha3(x)

@public
def try32(inp: bytes32) -> bool:
    return sha3(inp) == sha3(self.test)
    