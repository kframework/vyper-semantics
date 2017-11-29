
x: num[4]

@public
def set():
    self.x = [3, 5, 7, 9]

@public
def data() -> num:
    for i in self.x:
        if i > 5:
            return i
    return -1
    