
@public
def foo() -> bytes <= 500:
    x = [1, 2, 3]
    return RLPList(x, [bytes])
    