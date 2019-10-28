from gmpy import gcd, invert
def eee(x, y):
    x, y = min(x, y), max(x, y)
    r, s, t = x, 1, 0
    R, S, T = y, 0, 1
    while r > 0 and R > 0:
        q = r/R
        new = r-q*R, s-q*S, t-q*T
        r, s, t = R, S, T
        R, S, T = new
    assert gcd(x, y) == r # gcd from euclidean algorithm
    assert r == x*s + y*t # s and t are the bezout coefficients
    inv = s + y*(s < 0) # modular inverse from bezout coefficient
    if r == 1:
        assert (x * inv) % y == 1
    return (r, s, t, inv)

assert [eee(i, 7)[3] for i in range(1, 7)] == [1, 4, 5, 2, 3, 6]
assert [invert(i, 7) for i in range(1, 7)] == [1, 4, 5, 2, 3, 6]
