
@public
def return_2_finney() -> wei_value:
    return as_wei_value(2, finney)

@public
def return_3_finney() -> wei_value:
    return as_wei_value(2 + 1, finney)

@public
def return_2p5_ether() -> wei_value:
    return as_wei_value(2.5, ether)

@public
def return_3p5_ether() -> wei_value:
    return as_wei_value(2.5 + 1, ether)

@public
def return_2pow64_wei() -> wei_value:
    return as_wei_value(18446744.073709551616, szabo)
    