
@public
def foo() -> timestamp[2]:
    return [block.timestamp + 86400, block.timestamp]
    