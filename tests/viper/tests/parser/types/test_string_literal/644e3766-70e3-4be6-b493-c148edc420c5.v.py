
moo: bytes <= 100

@public
def foo(s: num, L: num) -> bytes <= 100:
        x = 27
        r = slice("ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc", start=s, len=L)
        y = 37
        if x * y == 999:
            return r

@public
def bar(s: num, L: num) -> bytes <= 100:
        self.moo = "ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
        x = 27
        r = slice(self.moo, start=s, len=L)
        y = 37
        if x * y == 999:
            return r

@public
def baz(s: num, L: num) -> bytes <= 100:
        x = 27
        self.moo = slice("ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc", start=s, len=L)
        y = 37
        if x * y == 999:
            return self.moo
        