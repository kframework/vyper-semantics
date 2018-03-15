@public
def data() -> num:
    s = [1, 2, 3, 4, 5, 6]
    count = 0
    for i in s:
        s[count] = 1  # this should not be allowed.
        if i >= 3:
            return i
        count += 1
    return -1
