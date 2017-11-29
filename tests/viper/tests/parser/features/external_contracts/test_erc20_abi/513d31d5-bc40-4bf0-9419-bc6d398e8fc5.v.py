
token_address: address(ERC20)

@public
def __init__(token_addr: address):
    self.token_address = token_addr

@public
def symbol() -> bytes32:
    return self.token_address.symbol()

@public
def balanceOf(_owner: address) -> num256:
    return self.token_address.balanceOf(_owner)

@public
def totalSupply() -> num256:
    return self.token_address.totalSupply()

@public
def transfer(_to: address, _value: num256) -> bool:
    return self.token_address.transfer(_to, _value)

@public
def transferFrom(_from: address, _to: address, _value: num(num256)) -> bool:
    return self.token_address.transferFrom(_from, _to, _value)

@public
def allowance(_owner: address, _spender: address) -> num256:
    return self.token_address.allowance(_owner, _spender)
    