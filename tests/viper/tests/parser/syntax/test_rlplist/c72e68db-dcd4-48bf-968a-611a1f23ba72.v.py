
@public
def foo() -> bytes <= 500:
    x = RLPList('àxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx', [bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes, bytes])
    return x[1]
    