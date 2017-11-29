
x: bytes <= 100
@public
def foo() -> num256:
    self.x = "cowcowcowcowcowccowcowcowcowcowccowcowcowcowcowccowcowcowcowcowc"
    return extract32(self.x, 0, type=num256)
    