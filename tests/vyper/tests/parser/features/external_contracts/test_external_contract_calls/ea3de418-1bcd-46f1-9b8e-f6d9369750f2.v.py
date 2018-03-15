
lucky: public(num)

@public
def __init__(_lucky: num):
    self.lucky = _lucky

@public
def foo() -> num:
    return self.lucky

@public
def array() -> bytes <= 3:
    return 'dog'
    