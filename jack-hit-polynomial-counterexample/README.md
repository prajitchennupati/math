# Off the Real Line
### A counterexample to the real-rootedness of Jack hit polynomials

Prajit Chennupati (chennupati@gatech.edu) · Aashrith Nalam (analam3@gatech.edu)

📄 **Paper:** [`paper/paper.pdf`](paper/paper.pdf)

## The conjecture
Alexandersson, Haglund and Wang ([FPSAC 2018, arXiv:1805.00511](https://arxiv.org/abs/1805.00511);
[J. Comb. 2021, arXiv:1810.12763](https://arxiv.org/abs/1810.12763)), **Conjecture 1**: for
`J̃_μ^{(α)} = α^n J_μ^{(1/α)}` (integral-form Jack polynomial) and all partitions `μ, λ ⊢ n`, writing

```
⟨J̃_μ^{(α)}, s_λ⟩ = Σ_k a_k(μ,λ) · C(α+k, n),
```

(i) every `a_k(μ,λ)` is a nonnegative integer, and (ii) the *hit polynomial* `Σ_k a_k(μ,λ) z^k` has only real zeros.

## The result
For `μ = (8,8)`, `λ = (2⁸)` (n = 16), the hit polynomial `H(z)` has degree 12 with a simple zero at 0 and
**only 9 of its other 11 zeros real**; the remaining two are `−10.52898876935… ± 2.39070820941… i`.
A one-line certificate:

```
H′(−10)² < H(−10)·H″(−10),
```

which is impossible for a polynomial with only real zeros. **So part (ii) of Conjecture 1 is false.**

Scope: part (i) holds for this pair (all `a_k` are nonnegative integers), and the companion Conjecture 2
("rook" version) holds for it. Those statements remain open. An exhaustive exact search finds no other
failure of either conjecture for `n ≤ 17`, so n = 16 is the smallest counterexample.

## Verification
| What | How | Where |
|---|---|---|
| `⟨J̃_(8,8), s_(2⁸)⟩` as an exact polynomial in α, the `a_k`, and the root count | Exact rational arithmetic; Sturm count + rigorous Arb root isolation | [`paper/code/verify.py`](paper/code/verify.py) |
| Same polynomial by two other methods | Laplace–Beltrami recursion + inverse Kostka ([`jack.py`](paper/code/jack.py)); power-sum eigenvector + dual Jacobi–Trudi ([`independent/`](paper/code/independent/)) | `paper/code/` |
| Exhaustive search, n ≤ 17 | [`search.py`](paper/code/search.py) | `paper/code/` |
| Binomial expansion identity and non-real-rootedness of `H` | **Lean 4 + Mathlib**, axioms `propext`, `Classical.choice`, `Quot.sound` only; no `sorry` | [`lean-formalization/JackHit.lean`](lean-formalization/JackHit.lean) |

The Lean proof covers everything after the Jack polynomial computation. The identity
`p(α) = ⟨J̃_(8,8), s_(2⁸)⟩` is the computer-verified input, since Jack polynomials are not yet in Mathlib.

## Reproduce
```bash
pip install python-flint==0.9.0 sympy==1.14.0
python paper/code/verify.py            # < 1 s; prints the polynomial, a_k, root count, verdict
python paper/code/selftest.py          # sanity checks of the second implementation
python paper/code/independent/run_main.py

cd lean-formalization
lake exe cache get && lake build       # Lean 4 (toolchain in lean-toolchain), Mathlib v4.36.0
```

## Layout
```
paper/
  paper.pdf, paper.tex      the note
  code/                     verification scripts (exact arithmetic)
    independent/            third, independent implementation
lean-formalization/         standalone Lake project (Mathlib v4.36.0)
```

Not yet refereed — corrections welcome.
