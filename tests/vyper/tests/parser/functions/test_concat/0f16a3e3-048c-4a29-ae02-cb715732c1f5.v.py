
@public
def foo2(input1: bytes <= 50, input2: bytes <= 50) -> bytes <= 1000:
    return concat(input1, input2)

@public
def foo3(input1: bytes <= 50, input2: bytes <= 50, input3: bytes <= 50) -> bytes <= 1000:
    return concat(input1, input2, input3)
    