x: public(num(wei / sec))
y: public(num(wei / sec ** 2))
z: public(num(sec ** -1))

@public
def foo() -> num(sec ** 2):
    return self.x / self.y / self.z
