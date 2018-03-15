
s: bytes <= 100

@public
def foo():
    raw_log([], "moo")

@public
def goo():
    raw_log([0x1234567812345678123456781234567812345678123456781234567812345678], "moo2")

@public
def hoo():
    self.s = "moo3"
    raw_log([], self.s)

@public
def ioo(inp: bytes <= 100):
    raw_log([], inp)
    