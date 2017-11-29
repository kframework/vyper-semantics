
x: public(wei_value)
y: public(num[5])
z: public(bytes <= 100)
w: public({
    a: wei_value,
    b: num[7],
    c: bytes <= 100,
    d: num[address],
    e: num[3][3],
    f: timestamp,
    g: wei_value
}[num])

@public
def __init__():
    self.x = as_wei_value(7, wei)
    self.y[1] = 9
    self.z = "cow"
    self.w[1].a = 11
    self.w[1].b[2] = 13
    self.w[1].c = "horse"
    self.w[1].d[0x1234567890123456789012345678901234567890] = 15
    self.w[2].e[1][2] = 17
    self.w[3].f = 750
    self.w[3].g = 751
    