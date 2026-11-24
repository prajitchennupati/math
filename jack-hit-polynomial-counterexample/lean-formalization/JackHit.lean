import Mathlib

/-!
# A counterexample to Alexandersson–Haglund–Wang, Conjecture 1(ii)

Source: P. Alexandersson, J. Haglund, G. Wang, *On the Schur expansion of Jack polynomials*,
FPSAC 2018 (arXiv:1805.00511), full version arXiv:1810.12763. With `J̃_μ^{(α)} = α^n J_μ^{(1/α)}`,
Conjecture 1 writes `⟨J̃_μ, s_λ⟩ = Σ_k a_k(μ,λ) · C(α+k, n)` and asserts (ii): `Σ_k a_k z^k` has only
real zeros.

## What is formalized here
For `μ = (8,8)`, `λ = (2^8)`, `n = 16`, let `p` be the explicit polynomial below.
* `p_eq_binomial_expansion` : `p α = Σ_k a_k · C(α+k, 16)` for every rational `α`, with the explicit
  natural numbers `a_k` (so the expansion coefficients are these `a_k`; the basis `C(α+k,16)`,
  `k = 0..16`, is a basis of polynomials of degree `≤ 16`).
* `hitPoly_not_realRooted` : `H(z) = Σ_k a_k z^k` is **not** a real constant times a product of real
  linear factors `(z - r)`, i.e. it does not have only real zeros.

## What is NOT formalized (explicit hypothesis)
That `p α = ⟨J̃_{(8,8)}^{(α)}, s_{(2^8)}⟩`. Jack polynomials are not in Mathlib. This identity is
computer-verified with exact arithmetic by three independent implementations
(`../paper/code/verify.py`, `../paper/code/jack.py`, `../paper/code/independent/`). The conclusion "Conjecture 1(ii) fails" depends on it.

## Certificate for non-real-rootedness
If `f = c · ∏ (X - r_i)` with all `r_i` real then `f'(x)^2 - f(x) f''(x) ≥ 0` for every real `x`
(induction: multiplying by `X - r` sends this quantity `Q` to `p(x)^2 + (x-r)^2 Q`). For `H` at
`x = -10` the quantity is negative.
-/

open Polynomial

namespace JackHit

/-- The Laguerre-type quantity `f'(x)^2 - f(x) f''(x)`. -/
noncomputable def lag (f : ℝ[X]) (x : ℝ) : ℝ :=
  (f.derivative.eval x) ^ 2 - f.eval x * (f.derivative.derivative.eval x)

lemma lag_X_sub_C_mul (r : ℝ) (p : ℝ[X]) (x : ℝ) :
    lag ((X - C r) * p) x = (p.eval x) ^ 2 + (x - r) ^ 2 * lag p x := by
  simp only [lag, derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul, zero_mul, zero_add, eval_add, eval_mul, eval_sub, eval_X, eval_C]
  ring

lemma lag_C_mul_prod_nonneg (a : ℝ) (s : Multiset ℝ) (x : ℝ) :
    0 ≤ lag (C a * (s.map (fun r => X - C r)).prod) x := by
  induction s using Multiset.induction_on with
  | empty => simp [lag]
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm, lag_X_sub_C_mul]
    positivity

/-- `f` has only real zeros: it is a real constant times a product of real linear factors. -/
def RealRooted (f : ℝ[X]) : Prop :=
  ∃ (a : ℝ) (s : Multiset ℝ), f = C a * (s.map (fun r => X - C r)).prod

/-- A real-rooted real polynomial satisfies `f'(x)^2 ≥ f(x) f''(x)` everywhere. -/
lemma RealRooted.lag_nonneg {f : ℝ[X]} (hf : RealRooted f) (x : ℝ) : 0 ≤ lag f x := by
  obtain ⟨a, s, rfl⟩ := hf
  exact lag_C_mul_prod_nonneg a s x

/-- The coefficients `a_k((8,8),(2^8))`, `k = 0..16`, in the basis `C(α+k,16)`. -/
def a : ℕ → ℕ
  | 1 => 597793996800
  | 2 => 73236035174400
  | 3 => 2004440894668800
  | 4 => 19314619527168000
  | 5 => 79659352571904000
  | 6 => 154554571254988800
  | 7 => 146689299490406400
  | 8 => 68260823569612800
  | 9 => 15222991343616000
  | 10 => 1568059637760000
  | 11 => 68516388864000
  | 12 => 804722688000
  | _ => 0

/-- The Jack hit polynomial `H(z) = Σ_{k=0}^{16} a_k z^k` for `μ = (8,8)`, `λ = (2^8)`. -/
noncomputable def hitPoly : ℝ[X] :=
  ∑ k ∈ Finset.range 17, C (a k : ℝ) * X ^ k

/-- **Main theorem (Lean-verified part).** The hit polynomial is not real-rooted. -/
theorem hitPoly_not_realRooted : ¬ RealRooted hitPoly := by
  intro h
  have h1 := h.lag_nonneg (-10)
  have h2 : lag hitPoly (-10) < 0 := by
    simp only [lag, hitPoly, Finset.sum_range_succ, Finset.sum_range_zero, a]
    simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow, zero_mul, zero_add,
      eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_natCast, derivative_zero, eval_zero,
      derivative_natCast, map_natCast, Nat.cast_ofNat]
    norm_num
  linarith

/-- The polynomial `C(y, 16) = y (y-1) ⋯ (y-15) / 16!` evaluated at a rational `y`. -/
def binom16 (y : ℚ) : ℚ := (∏ i ∈ Finset.range 16, (y - i)) / 20922789888000

/-- `p(α) = ⟨J̃_{(8,8)}^{(α)}, s_{(2^8)}⟩` as computed (exactly) by `verify.py`. -/
def p (x : ℚ) : ℚ :=
  23296*x^16 - 397824*x^15 + 3058048*x^14 - 13633536*x^13 + 38899504*x^12 - 74989152*x^11
    + 94391024*x^10 - 52798368*x^9 - 25255216*x^8 + 15861216*x^7 + 2734928*x^6 + 141561504*x^5
    - 164654784*x^4 - 15603840*x^3 + 50803200*x^2

/-- The expansion of `p` in the basis `C(α+k,16)` has exactly the coefficients `a_k`. -/
theorem p_eq_binomial_expansion (x : ℚ) :
    p x = ∑ k ∈ Finset.range 17, (a k : ℚ) * binom16 (x + k) := by
  simp only [p, binom16, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, a]
  push_cast
  ring

end JackHit
