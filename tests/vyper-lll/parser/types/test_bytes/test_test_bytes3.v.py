x: num
maa: bytes <= 60
y: num
mbb: bytes <= 60

@public
def __init__():
    self.x = 27
    self.y = 37

@public
def set_maa(inp: bytes <= 60):
    self.maa = inp

@public
def set_maa2(inp: bytes <= 60):
    ay = inp
    self.maa = ay
    self.mbb = self.maa

@public
def get_maa() -> bytes <= 60:
    return self.maa

@public
def get_maa2() -> bytes <= 60:
    ay = self.maa
    return ay

@public
def get_xy() -> num:
    return self.x * self.y
