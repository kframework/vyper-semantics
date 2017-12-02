@public
def _num(x: num) -> num:
    return x

@public
def _num_add(x: num, y: num) -> num:
    return x + y

@public
def _num_sub(x: num, y: num) -> num:
    return x - y

@public
def _num_add3(x: num, y: num, z: num) -> num:
    return x + y + z

@public
def _num_max() -> num:
    return  170141183460469231731687303715884105727   #  2**127 - 1

@public
def _num_min() -> num:
    return -170141183460469231731687303715884105728   # -2**127
