@public
def double(x: num) -> num:
    return x * 2

@public
def returnten() -> num:
    return self.double(5)

@public
def _hashy(x: bytes32) -> bytes32:
    return sha3(x)

@public
def return_hash_of_rzpadded_cow() -> bytes32:
    return self._hashy(0x636f770000000000000000000000000000000000000000000000000000000000)
