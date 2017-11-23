@public
def augadd(x: num, y: num) -> num:
    z = x
    z += y
    return z

@public
def augmul(x: num, y: num) -> num:
    z = x
    z *= y
    return z

@public
def augsub(x: num, y: num) -> num:
    z = x
    z -= y
    return z

@public
def augdiv(x: num, y: num) -> num:
    z = x
    z /= y
    return z

@public
def augmod(x: num, y: num) -> num:
    z = x
    z %= y
    return z
