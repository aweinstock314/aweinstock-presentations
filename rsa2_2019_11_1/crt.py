from eea import eea
from gmpy import gcd
from itertools import combinations
def crt(eqns):
    assert len(eqns) >= 2
    assert [gcd(eqns[i][1], eqns[j][1]) == 1 for (i, j) in combinations(range(len(eqns)), 2)]
    a0, n0 = eqns[0]
    a1, n1 = eqns[1]
    _, m0, m1, _, _ = eea(n0, n1)
    assert m0*n0 + m1*n1 == 1
    x = (a0*m1*n1 + a1*m0*n0) % (n0 * n1)
    if len(eqns) > 2:
        x = crt([(x, n0*n1)]+eqns[2:])
    for (a, n) in eqns:
        assert x % n == a % n
    return x
