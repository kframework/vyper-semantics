
comb: num

@public
def __init__(x: num[2], y: bytes <= 3, z: num):
    self.comb = x[0] * 1000 + x[1] * 100 + len(y) * 10 + z

@public
def get_comb() -> num:
    return self.comb
    