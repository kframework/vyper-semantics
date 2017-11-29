
x3: num256[2]
y3: num256[2]

@public
def _ecadd(x: num256[2], y: num256[2]) -> num256[2]:
    return ecadd(x, y)

@public
def _ecadd2(x: num256[2], y: num256[2]) -> num256[2]:
    x2 = x
    y2 = [y[0], y[1]]
    return ecadd(x2, y2)

@public
def _ecadd3(x: num256[2], y: num256[2]) -> num256[2]:
    self.x3 = x
    self.y3 = [y[0], y[1]]
    return ecadd(self.x3, self.y3)

    