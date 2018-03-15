
allowed: num[10]

@public
def in_test(x: num) -> bool:
    self.allowed = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    if x in self.allowed:
        return True
    return False
    