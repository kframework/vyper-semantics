
@public
def foo() -> bytes <= 5:
    return "horse"

@public
def bar() -> bytes <= 10:
    return concat("b", "a", "d", "m", "i", "", "nton")

@public
def baz() -> bytes <= 40:
    return concat("0123456789012345678901234567890", "12")

@public
def baz2() -> bytes <= 40:
    return concat("01234567890123456789012345678901", "12")

@public
def baz3() -> bytes <= 40:
    return concat("0123456789012345678901234567890", "1")

@public
def baz4() -> bytes <= 100:
    return concat("01234567890123456789012345678901234567890123456789",
                  "01234567890123456789012345678901234567890123456789")
    