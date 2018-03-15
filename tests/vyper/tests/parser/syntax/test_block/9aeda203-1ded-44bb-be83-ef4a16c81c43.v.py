
a: num[timestamp]

@public
def add_record():
    self.a[block.timestamp] = block.timestamp + 20
    