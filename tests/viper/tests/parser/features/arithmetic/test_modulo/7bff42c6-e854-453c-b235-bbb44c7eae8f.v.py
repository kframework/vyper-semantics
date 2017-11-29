
@public
def num_modulo_num() -> num:
    return 1 % 2

@public
def decimal_modulo_decimal() -> decimal:
    return 1.5 % .33

@public
def decimal_modulo_num() -> decimal:
    return .5 % 1


@public
def num_modulo_decimal() -> decimal:
    return 1.5 % 1
