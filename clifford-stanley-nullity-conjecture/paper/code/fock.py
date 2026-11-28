# fock.py -- exact checks of Section 7 (Lemmas 19-20 and 22-25, Theorem 26: the screening operator J)
# in Lambda = Q[p_1,p_2,...].
# Elements: dict {partition (desc tuple): Fraction}.  Plethystic translation f[X - y]: p_r -> p_r - y^r.
# Usage: python fock.py M     (checks all degrees m <= M; the paper reports M = 13)
import sys, itertools
from fractions import Fraction as F
from math import factorial
import flint

M = int(sys.argv[1])

def partitions(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for a in range(min(n, mx), 0, -1):
        for r in partitions(n - a, a): yield (a,) + r
P = {n: list(partitions(n)) for n in range(M + 6)}
def zl(lam):
    out = 1
    for r in set(lam):
        c = lam.count(r); out *= r ** c * factorial(c)
    return out
def srt(t): return tuple(sorted(t, reverse=True))
def add(a, b, c=1):
    for k, v in b.items():
        a[k] = a.get(k, 0) + c * v
        if a[k] == 0: del a[k]
    return a
def mul(f, g):
    out = {}
    for a, x in f.items():
        for b, y in g.items():
            k = srt(a + b); out[k] = out.get(k, 0) + x * y
    return {k: v for k, v in out.items() if v}
def deg(lam): return sum(lam)

def Ek(k, f):     # derivation p_r -> r p_{r+k}
    out = {}
    for lam, c in f.items():
        for i, r in enumerate(lam):
            nl = srt(lam[:i] + (r + k,) + lam[i + 1:])
            out[nl] = out.get(nl, 0) + c * r
    return {k_: v for k_, v in out.items() if v}
def Qk(k): return {srt((a, k - a)): F(1) for a in range(1, k)} if k >= 2 else {}
def Qfull(k):
    out = {}
    for a in range(1, k):
        t = srt((a, k - a)); out[t] = out.get(t, 0) + 1
    return out
def frakE(k, f, c=0):
    out = Ek(k, f)
    add(out, mul(Qfull(k), f))
    if c: add(out, mul({(k,): F(1)}, f), -c)
    return out
def pk(k): return {(k,): F(1)}

def translate(f, sgn):  # f[X + sgn*y]  ->  dict s -> element (coefficient of y^s)
    out = {}
    for lam, c in f.items():
        n = len(lam)
        for mask in range(1 << n):
            keep = tuple(lam[i] for i in range(n) if not (mask >> i) & 1)
            s = sum(lam[i] for i in range(n) if (mask >> i) & 1)
            cnt = bin(mask).count("1")
            co = c * (sgn ** cnt)
            d = out.setdefault(s, {}); kk = srt(keep)
            d[kk] = d.get(kk, 0) + co
    return out
def Hpow(a, r):  # [z^r] H(z)^a = exp(a sum p_r z^r / r) = sum_{lam |- r} a^{l(lam)} p_lam / z_lam
    return {lam: F(a ** len(lam), zl(lam)) for lam in P[r]}

def resop(f, sgnT, a, shift):
    # Res_z z^{shift} H(z)^a f[X + sgnT / z]:  y=1/z, term z^{shift + r - s}; residue needs s = shift + r + 1
    T = translate(f, sgnT); out = {}
    top = max(T) if T else 0
    for s, g in T.items():
        r = s - shift - 1
        if r < 0: continue
        add(out, mul(Hpow(a, r), g))
    return {k: v for k, v in out.items() if v}
J    = lambda f: resop(f, -1, 2, 0)
Jm1  = lambda f: resop(f, +1, -2, -2)
Jp1  = lambda f: resop(f, -1, 2, 2)
Jm2  = lambda f: resop(f, +1, -2, -4)

def form(f, g):  # <p_lam,p_mu> = delta z_lam 2^{-l}
    return sum(c * g.get(l, 0) * F(zl(l), 2 ** len(l)) for l, c in f.items())

def hm(m): return {lam: F(1, zl(lam)) for lam in P[m]}
def em(m): return {lam: F((-1) ** (m - len(lam)), zl(lam)) for lam in P[m]}

def rank(vecs, n):
    vecs = [v for v in vecs if v]
    if not vecs: return 0
    idx = {l: i for i, l in enumerate(P[n])}
    Mx = flint.fmpq_mat(len(vecs), len(P[n]))
    for i, v in enumerate(vecs):
        for l, c in v.items(): Mx[i, idx[l]] = flint.fmpq(c.numerator, c.denominator)
    return Mx.rank()
def pcount(n): return len(P[n]) if n >= 0 else 0

ok = True
def chk(cond, msg):
    global ok
    if not cond: ok = False; print("FAIL", msg)

# --- Lemma 4.1 Newton identities, Lemma 4.2(a), Witt relations, J on h, e
for m in range(0, M + 1):
    for k in range(1, 5):
        lhs = add(Ek(k, hm(m)), mul(pk(k), hm(m)))
        rhs = {}; add(rhs, hm(m + k), m + k)
        for s in range(1, k): add(rhs, mul(pk(s), hm(m + k - s)), -1)
        chk(add(dict(lhs), rhs, -1) == {}, f"Newton h m={m} k={k}")
        lhs = add(Ek(k, em(m)), mul(pk(k), em(m)), -1)
        rhs = {}; add(rhs, em(m + k), m + k)
        for s in range(1, k): add(rhs, mul(pk(s), em(m + k - s)), -((-1) ** (s - 1)))
        rhs = {kk: v * (-1) ** k for kk, v in rhs.items()}
        chk(add(dict(lhs), rhs, -1) == {}, f"Newton e m={m} k={k}")
v = {(): F(1)}
for j in range(1, M + 1):
    v = frakE(1, v, c=1)
    target = {kk: c * F((-1) ** j * factorial(j)) for kk, c in em(j).items()}
    chk(add(dict(v), target, -1) == {}, f"Lemma 4.2a j={j}")
for m in range(1, M + 1):
    chk(add(J(hm(m)), hm(m - 1)) == {}, f"J h_m m={m}")
    chk(add(J({k: c * (-1) ** m for k, c in em(m).items()}), hm(m - 1), -1) == {}, f"J e_m m={m}")
print("Newton/Lemma4.2a/J(h),J(e) done:", ok)

# Witt relations for frakE on basis elements
for n in range(0, max(1, M - 5) + 1):
    for f in [{l: F(1)} for l in P[n]]:
        for a in range(1, 4):
            for b in range(a + 1, 5):
                lhs = add(frakE(a, frakE(b, f)), frakE(b, frakE(a, f)), -1)
                rhs = {kk: c * (b - a) for kk, c in frakE(a + b, f).items()}
                chk(add(dict(lhs), rhs, -1) == {}, f"Witt a={a} b={b} n={n}")
print("Witt relations [E_a,E_b]=(b-a)E_{a+b} for frakE:", ok)

# --- L = U(frakE).1 graded pieces, generated by all k
L = {0: [{(): F(1)}]}
for m in range(1, M + 1):
    vecs = []
    for k in range(1, m + 1):
        for f in L[m - k]: vecs.append(frakE(k, f))
    # reduce to a basis
    idx = {l: i for i, l in enumerate(P[m])}
    Mx = flint.fmpq_mat(len(vecs), len(P[m]))
    for i, vv in enumerate(vecs):
        for l, c in vv.items(): Mx[i, idx[l]] = flint.fmpq(c.numerator, c.denominator)
    R, rk = Mx.rref()
    L[m] = []
    for i in range(rk):
        d = {}
        for j, l in enumerate(P[m]):
            x = R[i, j]
            if x != 0: d[l] = F(int(x.p), int(x.q))
        L[m].append(d)
    chk(rk == pcount(m) - pcount(m - 1), f"dim L_m m={m}: {rk}")
    Cm = {}; add(Cm, hm(m), F(1, 2)); add(Cm, em(m), F((-1) ** m, 2))
    chk(rank(L[m] + [Cm], m) == rk, f"C_m in L_m m={m}")
    chk(all(J(f) == {} for f in L[m]), f"J(L_m)=0 m={m}")
    Jimg = [J({l: F(1)}) for l in P[m]]
    chk(rank(Jimg, m - 1) == pcount(m - 1), f"J surjective m={m}")
    # intertwining on basis
    for l in P[m - 1] if m - 1 >= 0 else []:
        f = {l: F(1)}
        for k in range(1, 4):
            lhs = J(frakE(k, f))
            rhs = add(frakE(k, J(f)), mul(pk(k), J(f)), 2)
            chk(add(dict(lhs), rhs, -1) == {}, f"intertwine k={k} f={l}")
    # commutator identity on Lambda_{m-1}, adjointness
    for l in P[m - 1]:
        f = {l: F(1)}
        lhs = add(J(Jm1(f)), Jm2(Jp1(f)), -1)
        chk(lhs == {l: F(2)}, f"J J^-_1 - J^-_2 J^+_1 = 2 on {l}")
    for l in P[m]:
        for l2 in P[m - 1]:
            chk(form(J({l: F(1)}), {l2: F(1)}) == form({l: F(1)}, Jm1({l2: F(1)})), "J^dag=J^-_1")
        if m >= 3:
            for l2 in P[m - 3]:
                chk(form(Jp1({l: F(1)}), {l2: F(1)}) == form({l: F(1)}, Jm2({l2: F(1)})), "(J^+_1)^dag=J^-_2")
    print(f"m={m}: dim L_m={rk} = p(m)-p(m-1)={pcount(m)-pcount(m-1)}; ok so far {ok}", flush=True)

# negative control: wrong sign in Q (E - Q) should break dim formula or C_m membership
def frakEbad(k, f):
    out = Ek(k, f); add(out, mul(Qfull(k), f), -1); return out
Lb = {0: [{(): F(1)}]}; bad = False
for m in range(1, min(M, 8) + 1):
    vecs = [frakEbad(k, f) for k in range(1, m + 1) for f in Lb[m - k]]
    Lb[m] = vecs
    Cm = {}; add(Cm, hm(m), F(1, 2)); add(Cm, em(m), F((-1) ** m, 2))
    if rank(vecs + [Cm], m) != rank(vecs, m): bad = True
print("negative control (E_k - Q_k) breaks C_m membership:", bad)
print("ALL_OK", ok)
