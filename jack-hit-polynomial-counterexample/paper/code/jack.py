"""Exact Jack polynomials and the Alexandersson–Haglund–Wang coefficients.

J~_mu^(alpha) := alpha^n J_mu^(1/alpha)  (integral form J, Macdonald Ch. VI).
<J~_mu, s_lam> = sum_{k=0}^{n} a_k C(alpha+k, n) = sum_{k=1}^{n} b_{n-k} C(alpha,k) k!.
P_kappa in the monomial basis via Stanley's recursion (Demmel–Koev form):
  c_{kappa,mu} = (2/alpha)/(rho_kappa - rho_mu) * sum_lam (l_i - l_j) c_{kappa,lam},
  rho_kappa = sum_i kappa_i (kappa_i - 1 - (2/alpha)(i-1)),
lam from mu by (mu_i, mu_j) -> (mu_i + t, mu_j - t), i<j, 1<=t<=mu_j, sorted, mu < lam <= kappa.
J_kappa = prod_{s in kappa} (alpha*arm(s) + leg(s) + 1) * P_kappa.
"""
from fractions import Fraction as Fr
from functools import lru_cache
from math import comb, factorial

def partitions(n, maxp=None):
    if maxp is None: maxp = n
    if n == 0: yield (); return
    for k in range(min(n, maxp), 0, -1):
        for rest in partitions(n-k, k): yield (k,) + rest

def dominates(a, b):  # a >= b in dominance
    sa = sb = 0
    for i in range(max(len(a), len(b))):
        sa += a[i] if i < len(a) else 0; sb += b[i] if i < len(b) else 0
        if sa < sb: return False
    return True

def conj(p):
    return tuple(sum(1 for x in p if x > j) for j in range(p[0])) if p else ()

def hookprod_J(kappa, alpha):
    kc = conj(kappa); r = Fr(1)
    for i, row in enumerate(kappa):
        for j in range(row):
            arm = row - j - 1; leg = kc[j] - i - 1
            r *= alpha*arm + leg + 1
    return r

def jack_J_monomial(kappa, alpha):
    """dict mu -> coefficient of m_mu in J_kappa^(alpha), alpha a Fraction > 0."""
    n = sum(kappa)
    def rho(p): return sum(p[i]*(p[i] - 1 - Fr(2, 1)/alpha*i) for i in range(len(p)))
    parts = [p for p in partitions(n) if dominates(kappa, p)]
    parts.sort(key=lambda p: [-x for x in p])   # lexicographically decreasing => kappa first
    c = {kappa: Fr(1)}
    rk = rho(kappa)
    for mu in parts[1:]:
        s = Fr(0); L = list(mu)
        for i in range(len(L)):
            for j in range(i+1, len(L)):
                for t in range(1, L[j]+1):
                    l = L[:]; l[i] += t; l[j] -= t
                    lam = tuple(sorted([x for x in l if x > 0], reverse=True))
                    if lam in c: s += (l[i] - l[j]) * c[lam]
        c[mu] = (Fr(2)/alpha) / (rk - rho(mu)) * s
    h = hookprod_J(kappa, alpha)
    return {mu: v*h for mu, v in c.items() if v != 0}

@lru_cache(maxsize=None)
def kostka_table(n):
    P = list(partitions(n)); idx = {p: i for i, p in enumerate(P)}
    # K[lam][nu] = #SSYT of shape lam, content nu, via horizontal strips
    @lru_cache(maxsize=None)
    def K(lam, nu):
        if not nu: return 1 if not lam else 0
        last = nu[-1]; rest = nu[:-1]; tot = 0
        # remove a horizontal strip of size `last` from lam
        def rec(i, rem, cur):
            nonlocal tot
            if i == len(lam):
                if rem == 0:
                    mu = tuple(x for x in cur if x > 0)
                    tot += K(mu, rest)
                return
            nxt = lam[i+1] if i+1 < len(lam) else 0
            for r in range(0, min(rem, lam[i]-nxt)+1):
                rec(i+1, rem-r, cur + [lam[i]-r])
        rec(0, last, [])
        return tot
    M = [[K(l, tuple(sorted(nu))) if True else 0 for nu in P] for l in P]   # content order irrelevant
    return P, idx, M

def schur_coeffs(mono, n):
    """f = sum_nu f_nu m_nu  ->  dict lam -> <f, s_lam>.  Solves f_nu = sum_lam d_lam K[lam][nu]."""
    P, idx, M = kostka_table(n)
    d = {}
    # K is unitriangular w.r.t. dominance; process lam in decreasing lex order
    for lam in P:
        v = mono.get(lam, Fr(0)) - sum(d[l]*M[idx[l]][idx[lam]] for l in d)
        d[lam] = v
    return {l: v for l, v in d.items() if v != 0}

def interp_values(n, mu):
    """values p_lam(alpha) = <J~_mu, s_lam> at alpha = 1..n+1 (exact)."""
    vals = {}
    for a in range(1, n+2):
        alpha = Fr(a)
        J = jack_J_monomial(mu, 1/alpha)
        S = schur_coeffs({k: v*alpha**n for k, v in J.items()}, n)
        for lam in partitions(n): vals.setdefault(lam, []).append(S.get(lam, Fr(0)))
    return vals

def solve(A, y):
    n = len(y); M = [row[:] + [y[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]/M[c][c]; M[r] = [x - f*z for x, z in zip(M[r], M[c])]
    return [M[i][n]/M[i][i] for i in range(n)]

def gen_binom(x, k):  # C(x, k) for rational x
    r = Fr(1)
    for i in range(k): r *= (x - i)
    return r / factorial(k)

def ahw_coeffs(n, vals):
    """from values at alpha=1..n+1 return (a_0..a_n), (b_0..b_n) with b_n := coefficient of C(alpha,0)0! (should be 0)."""
    pts = list(range(1, n+2))
    A1 = [[gen_binom(Fr(m + k), n) for k in range(n+1)] for m in pts]
    a = solve(A1, vals)
    A2 = [[gen_binom(Fr(m), k)*factorial(k) for k in range(0, n+1)] for m in pts]
    bb = solve(A2, vals)          # bb[k] = b_{n-k}
    b = [bb[n-j] for j in range(n+1)]  # b[j] = b_j
    return a, b
