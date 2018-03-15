
mom: {a: {c: num}[3], b:num}
qoq: {c: num}

@public
def foo() -> num:
    self.mom = {a: [{c: 1}, {c: 2}, {c: 3}], b: 4}
    non = {c: 5}
    self.mom.a[0] = non
    non = {c: 6}
    self.mom.a[2] = non
    return self.mom.a[0].c + self.mom.a[1].c * 10 + self.mom.a[2].c * 100 + self.mom.b * 1000

@public
def fop() -> num:
    popp = {a: [{c: 1}, {c: 2}, {c: 3}], b: 4}
    self.qoq = {c: 5}
    popp.a[0] = self.qoq
    self.qoq = {c: 6}
    popp.a[2] = self.qoq
    return popp.a[0].c + popp.a[1].c * 10 + popp.a[2].c * 100 + popp.b * 1000

@public
def foq() -> num:
    popp = {a: [{c: 1}, {c: 2}, {c: 3}], b: 4}
    popp.a[0] = None
    popp.a[2] = None
    return popp.a[0].c + popp.a[1].c * 10 + popp.a[2].c * 100 + popp.b * 1000
    