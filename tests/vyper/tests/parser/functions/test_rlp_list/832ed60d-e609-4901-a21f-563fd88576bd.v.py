
u: bytes <= 100

@public
def foo() -> address:
    x = RLPList('ö55555555555555555555 GGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG', [address, bytes32])
    return x[0]

@public
def fop() -> bytes32:
    x = RLPList('ö55555555555555555555 GGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG', [address, bytes32])
    return x[1]

@public
def foq() -> bytes <= 100:
    x = RLPList('Åcow', [bytes, num])
    return x[0]

@public
def fos() -> num:
    x = RLPList('Åcow', [bytes, num])
    return x[1]

@public
def fot() -> num256:
    x = RLPList('Åcow', [bytes, num256])
    return x[1]

@public
def qoo(inp: bytes <= 100) -> address:
    x = RLPList(inp, [address, bytes32])
    return x[0]

@public
def qos(inp: bytes <= 100) -> num:
    x = RLPList(inp, [num, num])
    return x[0] + x[1]

@public
def qot(inp: bytes <= 100):
    x = RLPList(inp, [num, num])

@public
def qov(inp: bytes <= 100):
    x = RLPList(inp, [num256, num256])

@public
def roo(inp: bytes <= 100) -> address:
    self.u = inp
    x = RLPList(self.u, [address, bytes32])
    return x[0]

@public
def too(inp: bytes <= 100) -> bool:
    x = RLPList(inp, [bool])
    return x[0]

@public
def voo(inp: bytes <= 1024) -> num:
    x = RLPList(inp, [num, num, bytes32, num, bytes32, bytes])
    return x[1]
    