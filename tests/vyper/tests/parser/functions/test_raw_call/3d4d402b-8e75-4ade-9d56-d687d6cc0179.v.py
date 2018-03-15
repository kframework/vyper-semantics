
@public
def create_and_call_returnten(inp: address) -> num:
    x = create_with_code_of(inp)
    o = extract32(raw_call(x, "Ð±¸", outsize=32, gas=50000), 0, type=num128)
    return o

@public
def create_and_return_forwarder(inp: address) -> address:
    x = create_with_code_of(inp)
    return x
    