
z: num[3]
z2: num[2][2]
z3: num[2]

@public
def foo(x: num[3]) -> num:
    return x[0] + x[1] + x[2]

@public
def goo(x: num[2][2]) -> num:
    return x[0][0] + x[0][1] + x[1][0] * 10 + x[1][1] * 10

@public
def hoo(x: num[3]) -> num:
    y = x
    return y[0] + x[1] + y[2]

@public
def joo(x: num[2][2]) -> num:
    y = x
    y2 = x[1]
    return y[0][0] + y[0][1] + y2[0] * 10 + y2[1] * 10

@public
def koo(x: num[3]) -> num:
    self.z = x
    return self.z[0] + x[1] + self.z[2]

@public
def loo(x: num[2][2]) -> num:
    self.z2 = x
    self.z3 = x[1]
    return self.z2[0][0] + self.z2[0][1] + self.z3[0] * 10 + self.z3[1] * 10
    