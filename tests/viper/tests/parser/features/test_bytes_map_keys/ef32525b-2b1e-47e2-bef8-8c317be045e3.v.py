
mapped_bytes: num[bytes <= 5]

@public
def set(v: num):
    self.mapped_bytes["test"] = v

@public
def get(k: bytes <= 5) -> num:
    return self.mapped_bytes[k]
    