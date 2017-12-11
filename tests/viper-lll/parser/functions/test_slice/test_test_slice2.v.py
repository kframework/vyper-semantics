@public
def slice_tower_test(inp1: bytes <= 50) -> bytes <= 50:
    inp = inp1
    for i in range(1, 11):
        inp = slice(inp, start=1, len=30 - i * 2)
    return inp
