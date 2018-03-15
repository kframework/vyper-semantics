addresses: address[3]

@public
def set(i: num, val: address):
    self.addresses[i] = val

@public
def ret(i: num) -> address:
    return self.addresses[i]

@public
def iterate_return_second() -> address:
    count = 0
    for i in self.addresses:
        count += 1
        if count == 2:
            return i
