
a: timestamp[timestamp]


@public
def add_record():
    self.a[block.timestamp] = block.timestamp + 20
    