
@public
def _hashy2(x: bytes <= 100) -> bytes32:
    return sha3(x)

@public
def return_hash_of_cow_x_30() -> bytes32:
    return self._hashy2("cowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcowcow")

@public
def _len(x: bytes <= 100) -> num:
    return len(x)

@public
def returnten() -> num:
    return self._len("badminton!")
    