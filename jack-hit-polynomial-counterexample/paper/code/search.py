"""Exact check of AHW Conjectures 1 and 2 (parts (i) integrality/nonnegativity and (ii) real-rootedness)
for all partitions mu, lam of n.  A(z) = sum_{k=0}^n a_k z^k ;  B(z) = sum_{k=0}^n b_{n-k} z^k.
Real-rootedness: exact Sturm count (sympy) of distinct real roots == degree of squarefree part,
after removing the factor z^m (zero is real)."""
import sys, time, json
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from jack import *
import sympy as sp
z = sp.Symbol('z')
def real_rooted(coeffs):
    c = [int(x) for x in coeffs]
    while c and c[-1] == 0: c.pop()
    if len(c) <= 2: return True
    P = sp.Poly(list(reversed(c)), z)
    sf = sp.Poly(sp.quo(P, sp.gcd(P, P.diff(z))), z)
    return sf.count_roots() == sf.degree()
n0, n1 = int(sys.argv[1]), int(sys.argv[2])
for n in range(n0, n1+1):
    T = time.time(); bad = []; npairs = 0; nonzero = 0
    for mu in partitions(n):
        vals = interp_values(n, mu)
        for lam, v in vals.items():
            npairs += 1
            if all(x == 0 for x in v): continue
            nonzero += 1
            a, b = ahw_coeffs(n, v)
            okA_i = all(x.denominator == 1 and x >= 0 for x in a)
            okB_i = all(x.denominator == 1 and x >= 0 for x in b)
            Bpoly = [b[n-k] for k in range(n+1)]     # coefficient of z^k is b_{n-k}
            okA_ii = okA_i and real_rooted(a)
            okB_ii = okB_i and real_rooted(Bpoly)
            if n == 3 and mu == (3,) and lam == (3,):
                print('  check mu=lam=(3): a =', a, ' B coeffs (z^0..z^n) =', Bpoly)
            if not (okA_i and okB_i and okA_ii and okB_ii):
                bad.append((mu, lam, [str(x) for x in a], [str(x) for x in Bpoly], okA_i, okA_ii, okB_i, okB_ii))
    print('n=%d: pairs %d (nonzero %d), failures %d, %.1fs' % (n, npairs, nonzero, len(bad), time.time()-T), flush=True)
    for x in bad[:10]: print('   FAIL', x, flush=True)
    if bad:
        json.dump(bad, open('failures_n%d.json' % n, 'w'))
