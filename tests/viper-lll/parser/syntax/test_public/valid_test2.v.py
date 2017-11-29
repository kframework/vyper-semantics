x: public(num(wei / sec))
y: public(num(wei / sec ** 2))
z: public(num(1 / sec))

@public
def foo() -> num(sec ** 2):
    return self.x / self.y / self.z
