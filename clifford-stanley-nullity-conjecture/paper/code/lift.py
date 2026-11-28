# lift.py -- Theorem 8 (lifting the top invariant), Section 6 of the paper.
# Builds the forest-Heine polynomial F(x,nu) FROM THE DEFINITION (enumeration of all labelled rooted
# forests on [m], iterated integration of Delta^2 with flint), forms F_d = sum_i h1^{d+i} mu^i [nu^i]F(e),
# e_k = c'_{k+1} - mu h1 l_k, with mu SYMBOLIC, and checks exactly in Lambda (dehomogenised at h1 = 1,
# which is injective on weight-homogeneous elements):
#   (P) polynomiality: every monomial prod h_{j+1}^{a_j} has weight sum (j+1)a_j <= n = d^2;
#   (K) D_V F_d = 0 for V = u^2/(1+mu u) (as a polynomial identity in mu);
#   (I) no component of length < d, and the length-d component is mu-free and proportional to T_d,
#       where T_d is computed independently as the kernel of D_{u^2} on Lambda_{d^2,d} (exact fmpq rref).
# Negative controls: flip the sign of nu in F, and drop the nu^1 level; both must fail (K) or (P).
# Usage: python lift.py d     (d = 2..7)
import sys, itertools, math, time
import flint
from fractions import Fraction as Fr

d = int(sys.argv[1]); m = d - 1; n = d * d; w = n - d
t0 = time.time()

# ---------- forests and the polynomial F(x, nu) ----------
def forests(m):
    for par in itertools.product(range(-1, m), repeat=m):
        ok = True
        for i in range(m):
            if par[i] == i: ok = False; break
        if not ok: continue
        for i in range(m):          # acyclicity
            seen = set(); j = i
            while j != -1:
                if j in seen: ok = False; break
                seen.add(j); j = par[j]
            if not ok: break
        if ok: yield par

sctx = flint.fmpq_mpoly_ctx.get(('s', max(m, 1)), 'lex')
S = sctx.gens()
Delta2 = sctx.from_dict({(0,) * max(m, 1): 1})
for i in range(m):
    for j in range(i + 1, m):
        Delta2 = Delta2 * (S[i] - S[j]) ** 2

def depth(par, i):
    k = 0
    while par[i] != -1: i = par[i]; k += 1
    return k

Fx = {}   # nch -> dict sorted-tuple-of-x-indices -> Fraction
nforest = 0
for par in forests(m):
    nforest += 1
    P = Delta2
    order = sorted([i for i in range(m) if par[i] != -1], key=lambda i: -depth(par, i))
    for c in order:
        P = P.integral(c)                       # int_0^{s_c}
        sub = [S[i] for i in range(m)]; sub[c] = S[par[c]]
        P = P.compose(*sub)                     # s_c := s_parent
    roots = [i for i in range(m) if par[i] == -1]
    nch = m - len(roots)
    D = Fx.setdefault(nch, {})
    for mon, cf in P.terms():
        for c in range(m):
            assert par[c] == -1 or mon[c] == 0
        key = tuple(sorted(int(mon[r]) + 1 for r in roots))
        D[key] = D.get(key, Fr(0)) + Fr(int(cf.p), int(cf.q))
assert nforest == (m + 1) ** (m - 1) if m >= 1 else True, nforest
mf = math.factorial(m)
levels = {}
for nch, D in Fx.items():
    levels[nch] = {k: (-1) ** nch * v / mf for k, v in D.items() if v != 0}
print(f"d={d}: {nforest} rooted forests (expected {(m+1)**(m-1)}); nu-levels {sorted(levels)}; "
      f"{time.time()-t0:.1f}s", flush=True)
# weight check of levels: sum (k+1) over x_k = w - i
for i, D in levels.items():
    for key in D: assert sum(k + 1 for k in key) == w - i
# Heine check: level 0 = det(x_{i+j-1})_{i,j<=m}
import sympy
X = sympy.symbols('x1:%d' % (2 * m + 2))
if m >= 1:
    H = sympy.Matrix(m, m, lambda i, j: X[i + j]).det()
    Hd = sympy.Poly(sympy.expand(H), *X).as_dict()
    hk = {}
    for mon, c in Hd.items():
        key = tuple(sorted(sum([[k + 1] * e for k, e in enumerate(mon)], [])))
        hk[key] = Fr(int(c))
    assert {k: v for k, v in hk.items() if v} == levels[0], "level 0 is not the Hankel determinant"
    print("level 0 == det(x_{i+j-1}) (Heine/Andreief): OK", flush=True)

def check(levels, label):
    K = max(max(key) for D in levels.values() for key in D)    # largest x index
    N = K + 1
    ctx = flint.fmpq_mpoly_ctx.get(('y', N + 1), 'lex')        # y0..y_{N-1} = h_2..h_{N+1}; last = mu
    g = ctx.gens(); Y = [None] + list(g[:N]); mu = g[N]
    one = ctx.from_dict({(0,) * (N + 1): 1}); zero = one - one
    # H(t) = 1 + sum y_j t^j  (= u/(h1 t) at h1 = 1)
    cp = [one] + [zero] * N; l = [zero] * (N + 1)
    for k in range(1, N + 1):
        cp[k] = -sum((Y[j] * cp[k - j] for j in range(1, k + 1)), zero)
    for k in range(1, N + 1):
        acc = k * Y[k]
        for j in range(1, k): acc = acc - j * l[j] * Y[k - j]
        l[k] = acc * flint.fmpq(1, k)
    e = [None] + [cp[k + 1] - mu * l[k] for k in range(1, N)]
    f = zero
    for i, D in levels.items():
        for key, c in D.items():
            term = ctx.from_dict({(0,) * (N + 1): flint.fmpq(c.numerator, c.denominator)}) * mu ** i
            for k in key: term = term * e[k]
            f = f + term
    # (P) polynomiality
    badP = [mon for mon, c in f.terms() if sum((j + 2) * int(mon[j]) for j in range(N)) > n]
    # (I) length grading: length = n - sum_j (j+1) mon[j]  (h_{j+2} = y_j has reduced weight j+1)
    def redw(mon): return sum((j + 1) * int(mon[j]) for j in range(N))
    lowlen = [mon for mon, c in f.terms() if redw(mon) > w]
    top = {mon: c for mon, c in f.terms() if redw(mon) == w}
    top_mu = [mon for mon in top if mon[N] != 0]
    # (K) D_V f = 0, V = u^2/(1+mu u) = sum_r (-mu)^r u^{r+2};  u = t + sum y_j t^{j+1}
    T = N + 2
    u = [zero, one] + [Y[j] if j <= N - 1 else zero for j in range(1, T - 1)]
    u = u[:T]
    def mul(a, b):
        c = [zero] * T
        for i, ai in enumerate(a):
            if ai.is_zero(): continue
            for j in range(T - i):
                if not b[j].is_zero(): c[i + j] = c[i + j] + ai * b[j]
        return c
    V = [zero] * T; pw = mul(u, u); r = 0
    while any(not x.is_zero() for x in pw):
        cf = (-mu) ** r
        V = [V[i] + cf * pw[i] for i in range(T)]
        pw = mul(pw, u); r += 1
    Df = zero
    for j in range(1, N + 1):        # y_j = h_{j+1}: D_V h_{j+1} = [t^{j+1}] V(u)
        dj = f.derivative(j - 1)
        if not dj.is_zero(): Df = Df + dj * V[j + 1]
    # sanity: D_V c'_1 = -h1 (c'_1 = -y_1 at h1 = 1), so the derivation is not trivially zero
    assert (-1 * V[2]) == -one, "D_V c'_1 != -h1"
    print(f"[{label}] terms(F_d)={len(f)}  nonpoly monomials={len(badP)}  length<d monomials={len(lowlen)}  "
          f"mu in length-d part={len(top_mu)}  D_V F_d == 0: {Df.is_zero()}  ({time.time()-t0:.1f}s)", flush=True)
    return f, top, badP, lowlen, top_mu, Df.is_zero(), N

f, top, badP, lowlen, top_mu, kerOK, N = check(levels, "lift")

# ---------- independent T_d: kernel of D_{u^2} on Lambda_{n,d} ----------
def parts_exact(n, k, mx=None):
    if mx is None: mx = n
    if k == 0:
        if n == 0: yield ()
        return
    for a in range(min(n - (k - 1), mx), 0, -1):
        for r in parts_exact(n - a, k - 1, a): yield (a,) + r
src = list(parts_exact(n, d)); tgt = list(parts_exact(n, d + 1)); ti = {p: i for i, p in enumerate(tgt)}
M = flint.fmpq_mat(len(tgt), len(src))
for jj, lam in enumerate(src):
    for pos, k in enumerate(lam):
        rest = lam[:pos] + lam[pos + 1:]
        for a in range(1, k):
            mu_ = tuple(sorted(rest + (a, k - a), reverse=True))
            M[ti[mu_], jj] += 1
R, rk = M.rref()
piv = []; r = 0
for c in range(len(src)):
    if r < rk and R[r, c] != 0: piv.append(c); r += 1
free = [c for c in range(len(src)) if c not in piv]
print(f"dim K_(n={n},d={d}) = {len(free)} (expected 1)")
assert len(free) == 1
fc = free[0]; vec = [flint.fmpq(0)] * len(src); vec[fc] = flint.fmpq(1)
for i, pc in enumerate(piv): vec[pc] = -R[i, fc]
Td = {}
for lam, c in zip(src, vec):
    if c == 0: continue
    mon = [0] * (N + 1)
    for k in lam:
        if k >= 2: mon[k - 2] += 1
    Td[tuple(mon)] = c
ratio = None; propOK = set(Td) == set(top)
if propOK:
    for mon in Td:
        q = top[mon] / Td[mon]
        if ratio is None: ratio = q
        elif q != ratio: propOK = False; break
print(f"length-d part of F_d proportional to T_d: {propOK} (ratio {ratio}); |T_d| = {len(Td)} monomials")
ok = (not badP) and (not lowlen) and (not top_mu) and kerOK and propOK
print(f"RESULT d={d}: {'LIFT VERIFIED' if ok else 'FAIL'}")

# ---------- negative controls ----------
if d >= 3:
    neg1 = {i: {k: (-1) ** i * v for k, v in D.items()} for i, D in levels.items()}
    r1 = check(neg1, "control: nu -> -nu in F")
    neg2 = {i: D for i, D in levels.items() if i != 1}
    r2 = check(neg2, "control: drop nu^1 level")
    for rr, lab in ((r1, 'nu->-nu'), (r2, 'drop nu^1')):
        failed = bool(rr[2]) or not rr[5]
        print(f"control {lab}: {'fails as it should' if failed else 'UNEXPECTEDLY PASSES'}")
print(f"total {time.time()-t0:.1f}s")
