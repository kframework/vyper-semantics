@public
def phooey(inp: decimal) -> decimal:
    x = 10000.0
    for i in range(4):
        x = x * inp
    return x

@public
def arg(inp: decimal) -> decimal:
    return inp

@public
def garg() -> decimal:
    x = 4.5
    x *= 1.5
    return x

@public
def harg() -> decimal:
    x = 4.5
    x *= 2
    return x

@public
def iarg() -> wei_value:
    x = as_wei_value(7, wei)
    x *= 2
    return x
