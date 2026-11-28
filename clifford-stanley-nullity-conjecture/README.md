# Dyck Paths in the Nullspace
### A proof of the Clifford–Stanley–Alexandersson conjecture on the power-sum to monomial transition matrix

Prajit Chennupati (chennupati@gatech.edu)

📄 **Paper:** [`paper/paper.pdf`](paper/paper.pdf)

## The conjecture
Let `R_n` be the matrix that expresses the power sums in the monomial basis,

```
p_λ = Σ_{μ ⊢ n} R_{λμ} m_μ      (λ, μ ⊢ n),
```

and let `D_n` be its diagonal. Clifford and Stanley ([*Bottom Schur functions*, EJC 2004,
arXiv:math/0311382](https://arxiv.org/abs/math/0311382)) computed the nullity of `R_n − D_n` for small `n`:
`1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 11, 15, 19, 24, …`. They had no conjecture for its value.

In 2019 Alexandersson observed that these numbers match [OEIS A129528](https://oeis.org/A129528) and recorded the
**conjecture** ([symmetric functions catalog](https://www.symmetricfunctions.com/schurMisc.htm)):

```
dim ker(R_n − D_n) = a(n),
```

where `a(n)` is the number of Dyck paths, of any length, whose peak x-coordinates sum to `n`.

## The result
**The conjecture is true for every n ≥ 1.** The paper proves a refinement as well.
Filter the nullspace by the length of partitions. The `d`-th graded piece then has dimension
`[q^{n−d}] C_d(q)`, where `C_d(q) = [2d choose d]_q / [d+1]_q` is MacMahon's q-Catalan number.
By MacMahon's theorem, these pieces count Dyck paths of semilength `d` by peak sum.

The proof has four steps.
1. **Reduction to a derivation.** The nullspace equals the invariants of a one-parameter group acting on power
   series `u = Σ h_k t^k`. The generator is the iterative logarithm of `u ↦ log(1+u)`.
2. **The leading term** `u²∂_u` (Theorem 5). Writing `u = v/w` turns its invariants into Plücker coordinates.
   Schur–Weyl duality and Chevalley's theorem then identify them with `Hom_{S_2d}(S^{(d,d)}, R_2d)^*`, where
   `R_2d` is the coinvariant algebra.
3. **Lifting the top invariant** (Theorem 8). The top invariant survives the full group. The lift is an explicit
   sum over rooted forests of Heine-type integrals.
4. **Cyclicity** (Theorem 9). Reparametrizations of `t` generate all invariants from the top one. This is proved
   in `H*(Gr(d, 2d))` with a screening operator on the `c = 1` Fock space.

## Verification
Every script uses exact arithmetic.

| What | Range | Where |
|---|---|---|
| `dim ker(R_n − D_n)` from the definition = A129528(n); `dim ker(T − I)` and `dim ker D_{u²}` agree | `n ≤ 17` | [`paper/code/verify.py`](paper/code/verify.py) |
| Kernel of `u²∂_u` by length = q-Catalan numbers; MacMahon's identity | `n ≤ 17`, `d ≤ 7`; `d ≤ 8` | [`paper/code/verify.py`](paper/code/verify.py) |
| T-invariant Plücker functions = fake degree of `S^{(d,d)}` (Theorem 5) | `d ≤ 4`, `n ≤ 12` | [`paper/code/plucker.py`](paper/code/plucker.py) |
| Normal form of the true generator: `a = −1/2`, `μ = 1/6` (Lemma 6) | to order 16 | [`paper/code/normal_form.py`](paper/code/normal_form.py) |
| Forest lift `F_d` of the top invariant: polynomial, in the kernel identically in `μ`, initial form `T_d` (Theorem 8) | `d ≤ 7` | [`paper/code/lift.py`](paper/code/lift.py) |
| Cyclicity `K_d = U(S)·T_d`, directly in `Λ` (Theorem 9) | `d ≤ 7` | [`paper/code/cyclicity.py`](paper/code/cyclicity.py) |
| Screening-operator identities: intertwining, `J(L) = 0`, `J J^∨ − A^∨A = 2`, adjoints, surjectivity (§7) | `m ≤ 13` | [`paper/code/fock.py`](paper/code/fock.py) |

The proof is complete for all `n`; these computations check its statements independently in the ranges listed.
There is no Lean formalization yet.

## Reproduce
```bash
pip install python-flint==0.9.0 sympy==1.14.0
python paper/code/verify.py 12          # ~1 min; 17 takes a few minutes
python paper/code/plucker.py 4 12
python paper/code/normal_form.py 16 10
python paper/code/lift.py 5             # d = 2..7 (d = 7 takes ~10 min)
python paper/code/cyclicity.py exact 1 6
python paper/code/fock.py 13
```

## Layout
```
paper/
  paper.pdf, paper.tex      the paper
  code/                     verification scripts (exact arithmetic)
```

Not yet refereed — corrections welcome.
