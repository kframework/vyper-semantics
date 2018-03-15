
var: {a: num, b: num}

@public
def __init__(a: num, b: num):
    self.var.a = a
    self.var.b = b

@public
def returnMoose() -> num:
    return self.var.a * 10 + self.var.b
    