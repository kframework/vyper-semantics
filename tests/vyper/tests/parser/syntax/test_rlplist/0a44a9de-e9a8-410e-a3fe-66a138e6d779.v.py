
@public
def foo() -> bytes32:
    x = RLPList('ö55555555555555555555 GGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG', [address, bytes32])
    return x[1]
    