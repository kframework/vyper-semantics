
class Bar():
    def bar() -> num: pass

@public
def bar() -> num:
    return 1

@public
def _stmt(x: address):
    Bar(x).bar()

@public
def _expr(x: address) -> num:
    return Bar(x).bar()
    