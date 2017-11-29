
@public
def foo() -> address:
    x = RLPList('ö55555555555555555555 GGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG', [address, bytes32])
    return x[1]
    