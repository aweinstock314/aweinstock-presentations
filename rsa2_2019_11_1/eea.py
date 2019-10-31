from gmpy import gcd
def eea(x, y):
    r, s, t = x, 1, 0
    R, S, T = y, 0, 1
    while R > 0:
        q = r/R
        new = r-q*R, s-q*S, t-q*T
        r, s, t = R, S, T
        R, S, T = new
    assert gcd(x, y) == r # gcd from euclidean algorithm
    assert r == x*s + y*t # s and t are the bezout coefficients
    xinvy = s + y*(s < 0) # modular inverse from bezout coefficients
    yinvx = t + x*(t < 0)
    if r == 1:
        assert (x * xinvy) % y == 1
        assert (y * yinvx) % x == 1
    return (r, s, t, xinvy, yinvx)

