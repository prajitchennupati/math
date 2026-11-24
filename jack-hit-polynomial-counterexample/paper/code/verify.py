"""Standalone exact verifier (independent of jack.py) for the candidate counterexample to
Alexandersson–Haglund–Wang Conjecture 1(ii):  mu = (8,8), lambda = (2^8), n = 16.

Method (all exact rational arithmetic, python-flint):
 1. Monomial <-> power-sum transition: p_r * m_lam computed combinatorially; L[rho][lam] = [m_lam] p_rho.
 2. For a Jack parameter beta, P_mu^{(beta)} is the unique  m_mu + sum_{nu < mu} c_nu m_nu  that is orthogonal
    to every m_rho, rho < mu (dominance), for <p_rho, p_sigma>_beta = z_rho beta^{l(rho)} delta.  (The set
    {nu < mu} is a down-set, so span{m_nu} = span{P_nu} there; this is Macdonald VI (4.7)-(4.8).)
    J_mu = P_mu scaled so that [m_{1^n}] J_mu = n!   (Macdonald VI (10.25)/(10.22) normalization).
 3. <f, s_lam> = sum_rho c_rho chi^lam(rho)  for f = sum_rho c_rho p_rho; chi by Murnaghan–Nakayama.
 4. p(alpha) := <J~_mu, s_lam> with J~_mu^{(alpha)} = alpha^n J_mu^{(1/alpha)}, evaluated at alpha = 1..n+2
    (n+2 points: degree <= n is checked by the extra point), interpolated exactly.
 5. Expand p(alpha) = sum_{k=0}^{n} a_k C(alpha+k, n); check a_k in N, and count real roots of
    A(z) = sum_k a_k z^k exactly (FLINT rigorous isolation + Sturm via sympy).
Run:  python verify.py   [optional args: mu lambda, e.g. 3 2,1]
"""
import sys
from functools import lru_cache
from math import factorial, comb
import flint
import sympy as sp

MU = (8, 8); LAM = (2,)*8
if len(sys.argv) > 2:
    MU = tuple(int(x) for x in sys.argv[1].split(',')); LAM = tuple(int(x) for x in sys.argv[2].split(','))
n = sum(MU); assert sum(LAM) == n

def partitions(m, maxp=None):
    if maxp is None: maxp = m
    if m == 0: yield (); return
    for k in range(min(m, maxp), 0, -1):
        for r in partitions(m-k, k): yield (k,) + r

def leq_dom(a, b):  # a <= b in dominance
    sa = sb = 0
    for i in range(max(len(a), len(b))):
        sa += a[i] if i < len(a) else 0; sb += b[i] if i < len(b) else 0
        if sa > sb: return False
    return True

PARTS = list(partitions(n)); IDX = {p: i for i, p in enumerate(PARTS)}; N = len(PARTS)

def mult_pr(r, f):
    """p_r * (sum_lam f[lam] m_lam) in the monomial basis."""
    out = {}
    for lam, c in f.items():
        L = list(lam) + [0]
        seen = set()
        for i, v in enumerate(L):
            if v in seen: continue
            seen.add(v)
            mu = L[:]; mu[i] = v + r
            mu = tuple(sorted([x for x in mu if x > 0], reverse=True))
            out[mu] = out.get(mu, 0) + c * mu.count(v + r)
    return out

# L[rho][lam] = [m_lam] p_rho  (integers)
Lm = flint.fmpq_mat(N, N)
for rho in PARTS:
    f = {(): 1}
    for r in rho: f = mult_pr(r, f)
    for lam, c in f.items(): Lm[IDX[rho], IDX[lam]] = c
Minv = Lm.inv()          # m_lam = sum_rho Minv[lam][rho] p_rho

def zee(rho):
    z = 1
    for v in set(rho): z *= v**rho.count(v) * factorial(rho.count(v))
    return z

@lru_cache(maxsize=None)
def chi(lam, rho):
    """Murnaghan–Nakayama via beta-sets; lam, rho partitions of the same size."""
    if not rho: return 1 if not lam else 0
    r = rho[0]; rest = rho[1:]
    k = len(lam); beta = [lam[i] + (k - 1 - i) for i in range(k)]
    bs = set(beta); tot = 0
    for b in beta:
        if b - r >= 0 and (b - r) not in bs:
            sign = (-1) ** sum(1 for x in beta if b - r < x < b)
            nb = sorted([x for x in beta if x != b] + [b - r], reverse=True)
            kk = len(nb); new = tuple(x for x in (nb[i] - (kk - 1 - i) for i in range(kk)) if x > 0)
            tot += sign * chi(new, rest)
    return tot

def J_in_p(mu, beta):
    """coefficients c_rho with J_mu^{(beta)} = sum_rho c_rho p_rho."""
    below = [p for p in PARTS if p != mu and leq_dom(p, mu)]
    k = len(below)
    W = flint.fmpq_mat(N, N)
    for s, rho in enumerate(PARTS): W[s, s] = zee(rho) * beta**len(rho)
    Mb = flint.fmpq_mat(k, N); mrow = flint.fmpq_mat(1, N)
    for i, rr in enumerate(below):
        for s in range(N): Mb[i, s] = Minv[IDX[rr], s]
    for s in range(N): mrow[0, s] = Minv[IDX[mu], s]
    MbW = Mb * W
    G = MbW * Mb.transpose()                      # G[i,j] = <m_below_i, m_below_j>_beta (symmetric)
    rhs = -(MbW * mrow.transpose())               # rhs[i] = -<m_below_i, m_mu>_beta
    c = G.solve(rhs)
    mono = {mu: flint.fmpq(1)}
    for j, nu in enumerate(below): mono[nu] = c[j, 0]
    one = tuple([1]*n)
    scale = flint.fmpq(factorial(n)) / mono[one]
    pc = [flint.fmpq(0)]*N
    for lam, v in mono.items():
        il = IDX[lam]
        for s in range(N):
            if Minv[il, s] != 0: pc[s] += scale * v * Minv[il, s]
    return pc

def schur_coeff(pc, lam):
    return sum(pc[s] * chi(lam, PARTS[s]) for s in range(N) if pc[s] != 0)

vals = []
for a in range(1, n+3):
    alpha = flint.fmpq(a)
    pc = J_in_p(MU, 1/alpha)
    vals.append(alpha**n * schur_coeff(pc, LAM))
    print('  alpha=%d done' % a, flush=True)
x = sp.Symbol('x')
pts = [(sp.Integer(i+1), sp.Rational(int(v.p), int(v.q))) for i, v in enumerate(vals)]
p = sp.Poly(sp.interpolate(pts[:n+1], x), x)
assert p.degree() <= n and p.eval(pts[n+1][0]) == pts[n+1][1], 'degree/consistency check failed'
# a_k: p(alpha) = sum_k a_k C(alpha+k, n)
A = sp.Matrix([[sp.binomial(sp.Integer(m) + k, n) for k in range(n+1)] for m in range(1, n+2)])
a = list(A.LUsolve(sp.Matrix([p.eval(m) for m in range(1, n+2)])))
print('mu =', MU, 'lambda =', LAM)
print('p(alpha) =', p.as_expr())
print('a_k =', a)
assert all(v.is_integer and v >= 0 for v in a), 'part (i) fails'
z = sp.Symbol('z')
Az = sp.Poly(sum(a[k]*z**k for k in range(n+1)), z)
core = sp.Poly(sp.cancel(Az.as_expr() / z**min(k for k in range(n+1) if a[k] != 0)), z)
nreal = core.count_roots()
print('A(z) = z^m * core(z), deg core = %d, distinct real roots (Sturm) = %d, squarefree = %s'
      % (core.degree(), nreal, sp.degree(sp.gcd(core, core.diff(z)), z) == 0))
fl = flint.fmpz_poly([int(c) for c in reversed(core.all_coeffs())])
print('FLINT enclosures of non-real roots:', [str(r) for r, m in fl.complex_roots() if not r.imag.contains(0)])
print('VERDICT: Conjecture 1(ii) %s for this pair.' % ('FAILS' if nreal < core.degree() else 'holds'))
