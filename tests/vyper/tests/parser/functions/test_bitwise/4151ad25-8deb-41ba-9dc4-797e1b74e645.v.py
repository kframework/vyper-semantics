
@public
def _bitwise_and(x: num256, y: num256) -> num256:
    return bitwise_and(x, y)

@public
def _bitwise_or(x: num256, y: num256) -> num256:
    return bitwise_or(x, y)

@public
def _bitwise_xor(x: num256, y: num256) -> num256:
    return bitwise_xor(x, y)

@public
def _bitwise_not(x: num256) -> num256:
    return bitwise_not(x)

@public
def _shift(x: num256, y: num) -> num256:
    return shift(x, y)
    