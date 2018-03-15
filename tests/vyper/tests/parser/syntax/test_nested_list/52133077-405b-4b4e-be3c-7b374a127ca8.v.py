
bar: num[3][3]

@public
def foo() -> num[3]:
    self.bar = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
    for x in self.bar:
        if x == [4, 5, 6]:
            return x
    