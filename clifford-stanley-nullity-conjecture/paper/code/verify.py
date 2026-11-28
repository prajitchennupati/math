"""Main verification for "Dyck Paths in the Nullspace" (exact integer/rational arithmetic only).

(i)   nullity_Q(R_n - D_n) straight from the definition p_lambda = sum_mu R_{lambda mu} m_mu,
      R_{lambda mu} computed by counting assignments of parts of lambda to the variables of x^mu.
(ii)  A129528(n) by enumeration of Dyck words (peak abscissae), the identity peak sum = d + valley maj,
      and MacMahon's identity sum_P q^{valley maj} = [2d,d]_q/[d+1]_q (Section 4).
(iii) dim ker(D: Lambda_{n,d} -> Lambda_{n,d+1}) for each (d, n), D = D_{u^2}, compared with
      [q^n] q^d [2d,d]_q/[d+1]_q (Theorem 5).
(iv)  Proposition 4: dim ker(T - I) on Lambda^n, T: h_k -> p_k/k, equals the nullity in (i),
      and R_{lambda lambda} = prod_i m_i(lambda)!.
Usage: python verify.py [NMAX]   (default 12; NMAX = 17 takes a few minutes)
"""
import sys
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import factorial, prod
from collections import Counter

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def rank_exact(rows):
    """Rank of a matrix of Fractions/ints via fraction-free elimination on a common-denominator copy."""
    M = [list(r) for r in rows]
    if not M:
        return 0
    # clear denominators row by row
    from math import lcm
    A = []
    for r in M:
        L = 1
        for x in r:
            if isinstance(x, Fraction):
                L = lcm(L, x.denominator)
        A.append([int(x * L) for x in r])
    nr, nc = len(A), len(A[0])
    rnk = 0
    prev = 1
    col = 0
    r = 0
    while r < nr and col < nc:
        piv = None
        for i in range(r, nr):
            if A[i][col] != 0:
                piv = i
                break
        if piv is None:
            col += 1
            continue
        A[r], A[piv] = A[piv], A[r]
        for i in range(r + 1, nr):
            for j in range(col + 1, nc):
                A[i][j] = (A[r][col] * A[i][j] - A[i][col] * A[r][j]) // prev
            A[i][col] = 0
        prev = A[r][col]
        r += 1
        col += 1
        rnk += 1
    return rnk


# ---------- (i) R from the definition -------------------------------------------------
def coeff_p_in_m(lam, mu):
    """Coefficient of x_1^{mu_1}...x_l^{mu_l} in p_lambda = number of maps parts(lam)->[l(mu)]
    with fibre sums mu_i. Counted by DP over parts."""
    l = len(mu)

    @lru_cache(maxsize=None)
    def go(i, rem):
        if i == len(lam):
            return 1 if all(r == 0 for r in rem) else 0
        tot = 0
        for j in range(l):
            if rem[j] >= lam[i]:
                nr = list(rem)
                nr[j] -= lam[i]
                tot += go(i + 1, tuple(nr))
        return tot
    return go(0, tuple(mu))


def nullity_R_minus_D(n):
    P = list(partitions(n))
    R = [[coeff_p_in_m(l, m) for m in P] for l in P]
    for i, l in enumerate(P):
        expect = prod(factorial(c) for c in Counter(l).values())
        assert R[i][i] == expect, (l, R[i][i], expect)
    A = [[R[i][j] if i != j else 0 for j in range(len(P))] for i in range(len(P))]
    return len(P) - rank_exact(A)


# ---------- (ii) Dyck paths ----------------------------------------------------------
def dyck_words(d):
    def rec(w, up, h):
        if len(w) == 2 * d:
            yield w
            return
        if up < d:
            yield from rec(w + 'U', up + 1, h + 1)
        if h > 0:
            yield from rec(w + 'D', up, h - 1)
    yield from rec('', 0, 0)


def peak_sum(w):
    return sum(i + 1 for i in range(len(w) - 1) if w[i] == 'U' and w[i + 1] == 'D')


def valley_maj(w):
    return sum(i + 1 for i in range(len(w) - 1) if w[i] == 'D' and w[i + 1] == 'U')


def polymul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                c[i + j] += x * y
    return c


def polydiv_exact(a, b):
    a = a[:]
    q = [0] * (len(a) - len(b) + 1)
    for i in range(len(q) - 1, -1, -1):
        c = Fraction(a[i + len(b) - 1], b[-1])
        assert c.denominator == 1
        q[i] = int(c)
        for j, y in enumerate(b):
            a[i + j] -= q[i] * y
    assert all(x == 0 for x in a)
    return q


def qint(k):
    return [1] * k


def qfact(k):
    r = [1]
    for i in range(1, k + 1):
        r = polymul(r, qint(i))
    return r


def qcatalan(d):
    num = qfact(2 * d)
    den = polymul(polymul(qfact(d), qfact(d)), qint(d + 1))
    return polydiv_exact(num, den)


# ---------- (iii) D_{u^2} kernel by (d, weight) -------------------------------------
def D_u2(mu):
    """D(h_mu) as Counter over sorted partitions (h_0 does not occur: i,j>=1)."""
    out = Counter()
    for i, k in enumerate(mu):
        rest = mu[:i] + mu[i + 1:]
        for a in range(1, k):
            key = tuple(sorted(rest + (a, k - a), reverse=True))
            out[key] += 1
    return out


def ker_D_u2(n, d):
    src = [m for m in partitions(n) if len(m) == d]
    tgt = [m for m in partitions(n) if len(m) == d + 1]
    if not src:
        return 0
    if not tgt:
        return len(src)
    idx = {m: i for i, m in enumerate(tgt)}
    rows = []
    for m in src:
        r = [0] * len(tgt)
        for k, c in D_u2(m).items():
            r[idx[k]] += c
        rows.append(r)
    return len(src) - rank_exact(rows)


# ---------- (iv) T: h_k -> p_k/k in h-basis ------------------------------------------
def mul(a, b):
    c = Counter()
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            c[tuple(sorted(k1 + k2, reverse=True))] += v1 * v2
    return c


def T_images(N):
    # u = sum h_k t^k ; log(1+u) = sum_j (-1)^{j-1} u^j / j ; truncate at t^N
    # represent series as list over t-degree of Counters over partitions
    u = [Counter() for _ in range(N + 1)]
    for k in range(1, N + 1):
        u[k][(k,)] = Fraction(1)
    res = [Counter() for _ in range(N + 1)]
    powj = [Counter() for _ in range(N + 1)]
    powj[0][()] = Fraction(1)
    for j in range(1, N + 1):
        new = [Counter() for _ in range(N + 1)]
        for a in range(N + 1):
            if not powj[a]:
                continue
            for b in range(1, N + 1 - a):
                for k, v in mul(powj[a], u[b]).items():
                    new[a + b][k] += v
        powj = new
        for a in range(N + 1):
            for k, v in powj[a].items():
                res[a][k] += Fraction((-1) ** (j - 1), j) * v
    return res  # res[k] = p_k / k in h-basis


def kerT(n, Timg):
    P = list(partitions(n))
    idx = {m: i for i, m in enumerate(P)}
    rows = []
    for m in P:
        img = Counter({(): Fraction(1)})
        for k in m:
            img = mul(img, Timg[k])
        r = [Fraction(0)] * len(P)
        for k, v in img.items():
            r[idx[k]] += v
        r[idx[m]] -= 1
        rows.append(r)
    return len(P) - rank_exact(rows)


if __name__ == '__main__':
    # A129528 by enumeration up to NMAX: semilength d contributes only if min peak sum (=d) <= NMAX
    a = [0] * (NMAX + 1)
    for d in range(0, NMAX + 1):
        for w in dyck_words(d):
            s = peak_sum(w)
            if s <= NMAX:
                a[s] += 1
            # identity peak sum = d + valley maj
            assert s == d + valley_maj(w)
    print('A129528 (enumerated) n=0..', NMAX, ':', a)
    # MacMahon check
    for d in range(0, 9):
        cnt = Counter(valley_maj(w) for w in dyck_words(d))
        qc = qcatalan(d)
        assert [cnt.get(i, 0) for i in range(len(qc))] == qc and sum(cnt.values()) == sum(qc), d
    print('MacMahon valley-maj = [2d,d]/[d+1] verified for d<=8')

    # (iii)
    bad = []
    for d in range(1, 8):
        qc = qcatalan(d)
        ks = []
        for n in range(d, min(NMAX, d * d + 3) + 1):
            k = ker_D_u2(n, d)
            e = qc[n - d] if 0 <= n - d < len(qc) else 0
            ks.append(k)
            if k != e:
                bad.append((d, n, k, e))
        print(f'd={d}: ker dims n={d}..: {ks}  fake-degree coeffs: {qc[:len(ks)]}')
    print('(iii) mismatches:', bad)

    # (i) and (iv)
    Timg = T_images(NMAX)
    for n in range(1, NMAX + 1):
        nul = nullity_R_minus_D(n)
        kt = kerT(n, Timg)
        kd = sum(ker_D_u2(n, d) for d in range(1, n + 1))
        print(f'n={n}: nullity(R-D)={nul}  dimker(T-I)={kt}  dimker D_u2={kd}  A129528={a[n]}'
              + ('' if nul == kt == kd == a[n] else '   <-- MISMATCH'))
