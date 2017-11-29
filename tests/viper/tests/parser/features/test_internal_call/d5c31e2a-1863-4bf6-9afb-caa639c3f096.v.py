
@public
def summy(x: num, y: num) -> num:
    return x + y

@public
def catty(x: bytes <= 5, y: bytes <= 5) -> bytes <= 10:
    return concat(x, y)

@public
def slicey1(x: bytes <= 10, y: num) -> bytes <= 10:
    return slice(x, start=0, len=y)

@public
def slicey2(y: num, x: bytes <= 10) -> bytes <= 10:
    return slice(x, start=0, len=y)

@public
def returnten() -> num:
    return self.summy(3, 7)

@public
def return_mongoose() -> bytes <= 10:
    return self.catty("mon", "goose")

@public
def return_goose() -> bytes <= 10:
    return self.slicey1("goosedog", 5)

@public
def return_goose2() -> bytes <= 10:
    return self.slicey2(5, "goosedog")
    