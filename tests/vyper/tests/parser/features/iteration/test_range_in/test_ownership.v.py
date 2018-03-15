

owners: address[2]

@public
def __init__():
    self.owners[0] = msg.sender

@public
def set_owner(i: num, new_owner: address):
    assert msg.sender in self.owners
    self.owners[i] = new_owner

@public
def is_owner() -> bool:
    return msg.sender in self.owners
    