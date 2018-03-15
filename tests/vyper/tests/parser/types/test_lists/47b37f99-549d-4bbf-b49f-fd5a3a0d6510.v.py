
@public
def test_array(x: num, y: num, z: num, w: num) -> num:
    a: num[4]
    a[0] = x
    a[1] = y
    a[2] = z
    a[3] = w
    return a[0] * 1000 + a[1] * 100 + a[2] * 10 + a[3]
    