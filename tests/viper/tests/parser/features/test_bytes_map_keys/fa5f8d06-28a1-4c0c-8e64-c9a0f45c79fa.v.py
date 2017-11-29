
mapped_bytes: num[bytes <= 5]

@public
def set(k: bytes <= 5, v: num):
    self.mapped_bytes[k] = v

@public
def get(k: bytes <= 5) -> num:
    return self.mapped_bytes[k]
    