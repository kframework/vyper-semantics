s: num[6]

@public
def set():
    self.s = [1, 2, 3, 4, 5, 6]

@public
def data() -> num:
    count = 0
    for i in self.s:
        self.s[count] = 1  # this should not be allowed.
        if i >= 3:
            return i
        count += 1
    return -1
