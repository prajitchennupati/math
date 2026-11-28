# normal_form.py -- Lemma 6 (normal form) for the true generator.
#  (1) v = log of the composition operator g -> g(log(1+u)) (the iterative logarithm), exactly to order u^N;
#      a = v_2 = -1/2, mu = -v_3/v_2 = 1/6.
#  (2) solve psi(u) = u + O(u^2) with v(psi(u)) = psi'(u) * a u^2/(1+mu u) order by order (exact) and verify
#      the identity to order N.
#  (3) dim ker D_v on Lambda_n (exact) equals A129528(n) = sum_d [q^n] q^d [2d,d]/[d+1] for n <= NK,
#      and equals dim ker D_{V_mu}.
# Usage: python normal_form.py N NK     e.g. 16 10
import sys
from fractions import Fraction as F
import flint

N = int(sys.argv[1]); NK = int(sys.argv[2])

def smul(a, b, N):
    out = [F(0)] * (N + 1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j in range(0, N + 1 - i):
            if b[j]: out[i + j] += x * b[j]
    return out
def compose(g, f, N):  # g(f(u)), f(0)=0
    out = [F(0)] * (N + 1); pw = [F(1)] + [F(0)] * N
    for k in range(0, N + 1):
        if g[k]:
            for i in range(N + 1): out[i] += g[k] * pw[i]
        pw = smul(pw, f, N)
    return out
f = [F(0)] + [F((-1) ** (k - 1), k) for k in range(1, N + 1)]   # log(1+u)
# composition operator on span(u^1..u^N): column k = (u^k)(f)
C = [[F(0)] * N for _ in range(N)]
for k in range(1, N + 1):
    col = compose([F(0)] * k + [F(1)] + [F(0)] * (N - k), f, N)
    for i in range(1, N + 1): C[i - 1][k - 1] = col[i]
# log C = sum (-1)^{r-1} (C-I)^r / r  (nilpotent)
Nm = [[C[i][j] - (1 if i == j else 0) for j in range(N)] for i in range(N)]
def mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(N)) for j in range(N)] for i in range(N)]
logC = [[F(0)] * N for _ in range(N)]; Pw = Nm
for r in range(1, N + 1):
    for i in range(N):
        for j in range(N): logC[i][j] += F((-1) ** (r - 1), r) * Pw[i][j]
    Pw = mm(Pw, Nm)
v = [F(0)] + [logC[i][0] for i in range(N)]          # v = logC(u)
# check logC is the derivation g -> v g' on u^k
okder = True
for k in range(1, N + 1):
    vg = smul(v, [F(0)] * (k - 1) + [F(k)] + [F(0)] * (N - k + 1), N)
    for i in range(1, N + 1):
        if logC[i - 1][k - 1] != vg[i]: okder = False
print("v coefficients u^2..u^6:", [str(x) for x in v[2:7]], " logC is a derivation:", okder)
a = v[2]; mu = -v[3] / v[2]
print("a =", a, " mu =", mu)
# V = a u^2/(1+mu u)
V = [F(0)] * (N + 1)
for k in range(2, N + 1): V[k] = a * (-mu) ** (k - 2)
# solve psi = u + sum_{k>=2} c_k u^k with v(psi) = psi' V, order by order; coefficient of u^{k+1} is linear in c_k
psi = [F(0), F(1)] + [F(0)] * (N - 1)
def resid(psi):
    lhs = compose(v, psi, N)
    dpsi = [F(k + 1) * psi[k + 1] for k in range(N)] + [F(0)]
    rhs = smul(dpsi, V, N)
    return [x - y for x, y in zip(lhs, rhs)]
free = []
for k in range(2, N):
    r0 = resid(psi)[k + 1]
    psi[k] += 1; r1 = resid(psi)[k + 1]; psi[k] -= 1
    slope = r1 - r0
    if slope == 0:
        if r0 != 0: print("NORMAL FORM OBSTRUCTED at order", k + 1); break
        free.append(k)
    else:
        psi[k] = -r0 / slope + psi[k]
res = resid(psi)
print("normal form: free coefficients", free, " residual zero to order N:", all(x == 0 for x in res))

# ---- kernel dimensions on Lambda_n (h-basis, exact) for D_W, W a series in u
def partitions(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for a_ in range(min(n, mx), 0, -1):
        for r in partitions(n - a_, a_): yield (a_,) + r
def upow_coeffs(lam_max_len, n):
    pass
from functools import lru_cache
@lru_cache(maxsize=None)
def u_power(j, n):  # [t^m] u(t)^j for m<=n as dict partition->count (monomials in h)
    out = {}
    def rec(rem, parts, cnt):
        pass
    res = {}
    for m in range(j, n + 1):
        for lam in partitions(m):
            if len(lam) != j: continue
            # number of compositions with these parts = multinomial
            from math import factorial
            c = factorial(j)
            for x in set(lam): c //= factorial(lam.count(x))
            res.setdefault(m, {})[lam] = c
    return res
def kerdim(W, n):
    src = list(partitions(n)); ix = {p: i for i, p in enumerate(src)}
    M = flint.fmpq_mat(len(src), len(src))
    for jcol, lam in enumerate(src):
        # D_W h^lam = sum_pos (prod others) * [t^{lam_pos}] W(u)
        for pos in range(len(lam)):
            k = lam[pos]; rest = lam[:pos] + lam[pos + 1:]
            for jj in range(2, k + 1):
                if W[jj] == 0: continue
                for mono, c in u_power(jj, n).get(k, {}).items():
                    t = tuple(sorted(rest + mono, reverse=True))
                    x = W[jj] * c
                    M[ix[t], jcol] += flint.fmpq(x.numerator, x.denominator)
    return len(src) - M.rank()
def qbin(n, k):
    num = [1]
    for i in range(k):
        aa = [0] * (len(num) + n - i)
        for e, c in enumerate(num): aa[e] += c; aa[e + n - i] -= c
        m = i + 1
        for e in range(len(aa)):
            if e >= m: aa[e] += aa[e - m]
        while len(aa) > 1 and aa[-1] == 0: aa.pop()
        num = aa
    return num
def A129528(n):
    tot = 0
    for d in range(1, n + 1):
        b1 = qbin(2 * d, d); b2 = qbin(2 * d, d + 1)
        e = n - d
        x = (b1[e] if 0 <= e < len(b1) else 0) - (b2[e - 1] if 0 <= e - 1 < len(b2) else 0)
        tot += x
    return tot
ok = okder and all(x == 0 for x in res)
for n in range(1, NK + 1):
    kv = kerdim(v, n); kV = kerdim(V, n); A = A129528(n)
    print(f"n={n}: dim ker D_v = {kv}, dim ker D_(a V_mu) = {kV}, A129528 = {A}", flush=True)
    ok &= (kv == kV == A)
print("ALL_OK", ok)
