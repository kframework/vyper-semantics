y: {f1:num, f2:num}
def foo(x:num) -> num:
    self.y.f1 = x + 1
    self.y.f2 = self.y.f1 + 2
    return self.y.f2
