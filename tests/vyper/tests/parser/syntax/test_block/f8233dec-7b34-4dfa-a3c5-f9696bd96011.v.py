
a: timestamp[num]

@public
def add_record():
    self.a[block.timestamp] = block.timestamp + 20
    