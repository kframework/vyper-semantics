
mapped_bytes: num[bytes <= 4096]

@public
def set(k: bytes <= 4096, v: num):
    self.mapped_bytes[k] = v

@public
def get(k: bytes <= 4096) -> num:
    return self.mapped_bytes[k]
    