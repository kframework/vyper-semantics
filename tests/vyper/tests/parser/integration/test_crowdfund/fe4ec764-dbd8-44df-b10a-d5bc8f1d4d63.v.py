

funders: {sender: address, value: wei_value}[num]
nextFunderIndex: num
beneficiary: address
deadline: timestamp
goal: wei_value
refundIndex: num
timelimit: timedelta

@public
def __init__(_beneficiary: address, _goal: wei_value, _timelimit: timedelta):
    self.beneficiary = _beneficiary
    self.deadline = block.timestamp + _timelimit
    self.timelimit = _timelimit
    self.goal = _goal

@public
@payable
def participate():
    assert block.timestamp < self.deadline
    nfi = self.nextFunderIndex
    self.funders[nfi] = {sender: msg.sender, value: msg.value}
    self.nextFunderIndex = nfi + 1

@public
@constant
def expired() -> bool:
    return block.timestamp >= self.deadline

@public
@constant
def timestamp() -> timestamp:
    return block.timestamp

@public
@constant
def deadline() -> timestamp:
    return self.deadline

@public
@constant
def timelimit() -> timedelta:
    return self.timelimit

@public
@constant
def reached() -> bool:
    return self.balance >= self.goal

@public
def finalize():
    assert block.timestamp >= self.deadline and self.balance >= self.goal
    selfdestruct(self.beneficiary)

@public
def refund():
    ind = self.refundIndex
    for i in range(ind, ind + 30):
        if i >= self.nextFunderIndex:
            self.refundIndex = self.nextFunderIndex
            return
        send(self.funders[i].sender, self.funders[i].value)
        self.funders[i] = None
    self.refundIndex = ind + 30

    