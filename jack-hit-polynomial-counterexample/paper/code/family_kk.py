import sys, time
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from jack import *
import sympy as sp
x, z = sp.symbols('alpha z')
K = int(sys.argv[1]) if len(sys.argv) > 1 else 11
for k in range(2, K+1):
    n = 2*k; mu = (k, k); lam = (2,)*k
    T = time.time()
    v = interp_values(n, mu)[lam]
    p = sp.interpolate(list(zip(range(1, n+2), [sp.Rational(t.numerator, t.denominator) for t in v])), x)
    a, b = ahw_coeffs(n, v)
    A = sp.Poly(sum(int(a[i])*z**i for i in range(n+1)), z)
    m = min(i for i in range(n+1) if a[i] != 0)
    core = sp.Poly(sp.cancel(A.as_expr()/z**m), z)
    print('k=%d: p(alpha) = %s' % (k, sp.factor(p)), flush=True)
    print('      deg core %d, real roots %d   (%.1fs)' % (core.degree(), core.count_roots(), time.time()-T), flush=True)
