"""Reviewer's independent computation of <J~_mu, s_lambda>, J~ = alpha^n J_mu^{(1/alpha)}.
Method: Laplace-Beltrami operator in the POWER-SUM basis (no monomial basis, no Kostka, no
Murnaghan-Nakayama): J_mu^{(a)} = kernel of (D(a) - e_mu(a)) in degree n, normalised so that the
coefficient of p_1^n is 1 (== [m_{1^n}]J = n!, since only p_1^n contains m_{1^n}).
Schur functions via dual Jacobi-Trudi s_lam = det(e_{lam'_i-i+j}) computed in the p-basis.
Exact arithmetic (python-flint fmpq / fmpq_mat)."""
import sys
from math import factorial
from functools import lru_cache
import flint
from flint import fmpq, fmpq_mat

def parts(m, mx=None):
    mx = m if mx is None else mx
    if m == 0: yield (); return
    for k in range(min(m, mx), 0, -1):
        for r in parts(m-k, k): yield (k,)+r
def conj(l):
    return tuple(sum(1 for x in l if x > i) for i in range(l[0])) if l else ()
def nfun(l): return sum(i*x for i, x in enumerate(l))
def zee(r):
    z = 1
    for v in set(r): z *= v**r.count(v)*factorial(r.count(v))
    return z
def srt(t): return tuple(sorted(t, reverse=True))

def Dmatrix(n, a):
    P = list(parts(n)); idx = {p: i for i, p in enumerate(P)}
    M = fmpq_mat(len(P), len(P))   # M[row=target, col=source]
    for src in P:
        s = idx[src]; mult = {v: src.count(v) for v in set(src)}
        out = {}
        def add(t, c):
            t = srt(t); out[t] = out.get(t, 0) + c
        # C: (a-1)/2 sum i(i-1) p_i d_i
        add(src, fmpq(1, 2)*(a-1)*sum(v*(v-1)*m for v, m in mult.items()))
        # A: a/2 sum_{i,j} i j p_{i+j} d_i d_j
        for i in mult:
            for j in mult:
                if i == j:
                    if mult[i] < 2: continue
                    c = mult[i]*(mult[i]-1)
                else: c = mult[i]*mult[j]
                rest = list(src); rest.remove(i); rest.remove(j)
                add(rest+[i+j], fmpq(1, 2)*a*i*j*c)
        # B: 1/2 sum_{i,j>=1} (i+j) p_i p_j d_{i+j}
        for k, m in mult.items():
            for i in range(1, k):
                j = k-i
                rest = list(src); rest.remove(k)
                add(rest+[i, j], fmpq(1, 2)*k*m)
        for t, c in out.items(): M[idx[t], s] += c
    return P, idx, M

def jack_p(mu, a, cache={}):
    """J_mu^{(a)} as dict rho->coeff in power sums, coefficient of p_1^n = 1 (a Fraction-like fmpq)."""
    n = sum(mu); P, idx, M = Dmatrix(n, a)
    e = a*nfun(conj(mu)) - nfun(mu)
    N = len(P)
    A = M - e*fmpq_mat(N, N, [1 if i == j else 0 for i in range(N) for j in range(N)])
    R, rank = A.rref()
    assert N - rank == 1, ('eigenspace dim', N-rank)
    piv = []
    for r in range(rank):
        c = 0
        while R[r, c] == 0: c += 1
        piv.append(c)
    free = [c for c in range(N) if c not in piv][0]
    v = [fmpq(0)]*N; v[free] = fmpq(1)
    for r, c in enumerate(piv): v[c] = -R[r, free]
    v1 = v[idx[tuple([1]*n)]]
    assert v1 != 0
    return {P[i]: v[i]/v1 for i in range(N) if v[i] != 0}

# ---- Schur via dual Jacobi-Trudi in the p basis
def pmul(f, g):
    out = {}
    for r, c in f.items():
        for s, d in g.items():
            t = srt(r+s); out[t] = out.get(t, 0)+c*d
    return out
def padd(f, g, sg=1):
    out = dict(f)
    for r, c in g.items(): out[r] = out.get(r, 0)+sg*c
    return out
@lru_cache(None)
def e_p(k):
    if k < 0: return {}
    if k == 0: return {(): fmpq(1)}
    return {r: fmpq((-1)**(k-len(r)), zee(r)) for r in parts(k)}
def schur_p(lam):
    lc = conj(lam); m = len(lc)
    # det via Laplace expansion (small m ok) -- permutations expansion
    from itertools import permutations
    def sign(p):
        s = 1
        for i in range(len(p)):
            for j in range(i+1, len(p)):
                if p[i] > p[j]: s = -s
        return s
    tot = {}
    for p in permutations(range(m)):
        term = {(): fmpq(1)}
        for i in range(m):
            term = pmul(term, e_p(lc[i]-i+p[i]))
            if not term: break
        if term: tot = padd(tot, term, sign(p))
    return tot

def pairing(f, g):   # Hall inner product
    return sum(c*g.get(r, 0)*zee(r) for r, c in f.items())

def jt_coeff(mu, lam, alpha):
    """<alpha^n J_mu^{(1/alpha)}, s_lam> at rational alpha"""
    n = sum(mu)
    J = jack_p(mu, 1/fmpq(alpha))
    return fmpq(alpha)**n*pairing(J, schur_p(lam))

if __name__ == '__main__':
    pass
