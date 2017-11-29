
readings: decimal[3]

@public
def set(i: num, val: decimal):
    self.readings[i] = val

@public
def ret(i: num) -> decimal:
    return self.readings[i]

@public
def i_return(break_count: num) -> decimal:
    count = 0
    for i in self.readings:
        if count == break_count:
            return i
        count += 1
    