
counter: num

@public
def increment():
    self.counter += 1

@public
def returnten() -> num:
    for i in range(10):
        self.increment()
    return self.counter
    