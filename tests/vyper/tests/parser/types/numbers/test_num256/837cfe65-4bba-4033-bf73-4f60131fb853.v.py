
@public
def _num256_to_num(x: num(num256)) -> num:
    return x

@public
def _num256_to_num_call(x: num256) -> num:
    return self._num256_to_num(x)

@public
def built_in_conversion(x: num256) -> num:
    return as_num128(x)
    