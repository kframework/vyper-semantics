
x3: num256[2]
y3: num256

@public
def _ecmul(x: num256[2], y: num256) -> num256[2]:
    return ecmul(x, y)

@public
def _ecmul2(x: num256[2], y: num256) -> num256[2]:
    x2 = x
    y2 = y
    return ecmul(x2, y2)

@public
def _ecmul3(x: num256[2], y: num256) -> num256[2]:
    self.x3 = x
    self.y3 = y
    return ecmul(self.x3, self.y3)

