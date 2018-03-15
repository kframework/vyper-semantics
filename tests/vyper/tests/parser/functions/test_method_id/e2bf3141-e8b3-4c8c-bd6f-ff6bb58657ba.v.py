
@public
def double(x: num) -> num:
    return x * 2

@public
def returnten() -> num:
    ans = raw_call(self, concat(method_id("double(int128)"), as_bytes32(5)), gas=50000, outsize=32)
    return as_num128(extract32(ans, 0))
    