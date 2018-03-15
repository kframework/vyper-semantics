@public
def augadd(x: int128, y: int128) -> int128:
    z: int128 = x
    z += y
    return z

@public
def augmul(x: int128, y: int128) -> int128:
    z: int128 = x
    z *= y
    return z

@public
def augsub(x: int128, y: int128) -> int128:
    z: int128 = x
    z -= y
    return z

@public
def augmod(x: int128, y: int128) -> int128:
    z: int128 = x
    z %= y
    return z
