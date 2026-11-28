"""Theorem 5, step (b): the T-invariant degree-d Pluecker functions of each weight n, computed directly,
compared with the fake degree q^d [2d,d]_q/[d+1]_q.
Usage: python plucker.py [DMAX] [NMAX]   (default 3 9; the paper reports 4 12)
"""
import sys
from itertools import combinations, combinations_with_replacement
import sympy as sp

DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3
NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 9


def run(d, n):
    m = n + 2
    v = sp.symbols(f'v0:{m}')
    w = sp.symbols(f'w0:{m}')
    gens = list(v) + list(w)
    pairs = [(i, j) for i in range(m) for j in range(i + 1, m)]
    minor = {(i, j): v[i] * w[j] - v[j] * w[i] for (i, j) in pairs}
    mons = [c for c in combinations_with_replacement(pairs, d) if sum(i + j for i, j in c) == n]
    if not mons:
        return 0
    polys = [sp.Poly(sp.Mul(*[minor[p] for p in c]), *gens) for c in mons]
    # basis of span (Plucker relations): row-reduce coefficient vectors
    allm = sorted({mm for P in polys for mm in P.as_dict()})
    mi = {mm: i for i, mm in enumerate(allm)}
    rows = []
    for P in polys:
        r = [0] * len(allm)
        for mm, c in P.as_dict().items():
            r[mi[mm]] = c
        rows.append(r)
    M = sp.Matrix(rows)
    _, piv = M.T.rref()
    basis = [polys[i] for i in piv]
    dim = len(basis)

    # T_k derivation: x_j -> x_{j-k} for x in {v, w}
    def Tk(P, k):
        e = P.as_expr()
        out = 0
        for j in range(k, m):
            out += sp.diff(e, v[j]) * v[j - k] + sp.diff(e, w[j]) * w[j - k]
        return sp.Poly(sp.expand(out), *gens)
    imgs = []
    for P in basis:
        col = {}
        for k in range(1, n + 1):
            for mm, c in Tk(P, k).as_dict().items():
                col[(k, mm)] = c
        imgs.append(col)
    keys = sorted({kk for c in imgs for kk in c})
    if not keys:
        return dim
    A = sp.Matrix([[c.get(kk, 0) for kk in keys] for c in imgs])
    return dim - A.rank()


if __name__ == '__main__':
    for d in range(1, DMAX + 1):
        print(d, [run(d, n) for n in range(d, NMAX + 1)], flush=True)
