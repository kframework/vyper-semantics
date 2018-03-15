
mom: {a: {c: num}[3], b: num}
non: {a: {c: decimal}[3], b:num}
pap: decimal[2][2]

@public
def foo() -> num:
    self.mom = {a: [{c: 1}, {c: 2}, {c: 3}], b: 4}
    self.non = self.mom
    return floor(self.non.a[0].c + self.non.a[1].c * 10 + self.non.a[2].c * 100 + self.non.b * 1000)

@public
def goo() -> num:
    self.pap = [[1, 2], [3, 4.0]]
    return floor(self.pap[0][0] + self.pap[0][1] * 10 + self.pap[1][0] * 100 + self.pap[1][1] * 1000)
    