
z: num[2]

@public
def foo() -> num[2]:
    return [3, 5]

@public
def goo() -> num[2]:
    x = [3, 5]
    return x

@public
def hoo() -> num[2]:
    self.z = [3, 5]
    return self.z

@public
def joo() -> num[2]:
    self.z = [3, 5]
    x = self.z
    return x

@public
def koo() -> num[2][2]:
    return [[1,2],[3,4]]

@public
def loo() -> num[2][2]:
    x = [[1,2],[3,4]]
    return x

@public
def moo() -> num[2][2]:
    x = [1,2]
    return [x,[3,4]]

@public
def noo(inp: num[2]) -> num[2]:
    return inp

@public
def poo(inp: num[2][2]) -> num[2][2]:
    return inp

@public
def qoo(inp: num[2]) -> num[2][2]:
    return [inp,[3,4]]

@public
def roo(inp: num[2]) -> decimal[2][2]:
    return [inp,[3,4]]
    