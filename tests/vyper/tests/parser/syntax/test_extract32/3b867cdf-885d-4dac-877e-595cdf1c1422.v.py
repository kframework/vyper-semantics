
x: bytes <= 100
@public
def foo() -> num256:
    self.x = "cowcowcowcowcowccowcowcowcowcowccowcowcowcowcowccowcowcowcowcowc"
    return extract32(self.x, 1, type=num256)
