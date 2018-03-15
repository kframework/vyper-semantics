
mapped_bytes: num[bytes <= 34]

@public
def set(k: bytes <= 34, v: num):
    self.mapped_bytes[k] = v

@public
def get(k: bytes <= 34) -> num:
    return self.mapped_bytes[k]
    