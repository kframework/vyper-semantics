
x: decimal

@public
def foo():
    send(0x1234567890123456789012345678901234567890, as_wei_value(floor(self.x), wei))
    