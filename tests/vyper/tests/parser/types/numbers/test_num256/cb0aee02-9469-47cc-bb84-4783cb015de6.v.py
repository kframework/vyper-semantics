
@public
def exp(base: num256, exponent: num256, modulus: num256) -> num256:
      o = as_num256(1)
      for i in range(256):
          o = num256_mulmod(o, o, modulus)
          if bitwise_and(exponent, shift(as_num256(1), 255 - i)) != as_num256(0):
              o = num256_mulmod(o, base, modulus)
      return o
    