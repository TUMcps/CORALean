module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# Polynomials dominated coefficientwise

`P ≼ A` when `|aⱼ| ≤ bⱼ` for every coefficient. Dominance survives sums, products and
derivatives, and gives `|P y| ≤ A |y|`: the way to bound a polynomial that a recursion
built, from the recursion run on absolute values of its coefficients. It is what bounds
the high derivatives of `tanh`, `tan`, `atan`, `asin` and `acos`, each a polynomial in a
variable whose range is known.

## Inputs
* `A` – polynomial
* `a` – lower evaluation point
* `b` – upper evaluation point

## Hypotheses
* `h` – `A` dominates itself, so its coefficients are nonnegative
* `ha` – the lower point is nonnegative
* `hab` – the lower point is at most the upper one

## Conclusion
* `A` at the lower point is at most `A` at the upper point
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Polynomial

/-- `P` is dominated by `A`: every coefficient of `P` is at most that of `A` in magnitude. -/
def CoeffDom (P A : ℝ[X]) : Prop := ∀ j, |P.coeff j| ≤ A.coeff j


-- a dominating polynomial has nonnegative coefficients
theorem CoeffDom.nonneg {P A : ℝ[X]} (h : CoeffDom P A) (j : ℕ) : 0 ≤ A.coeff j :=
  le_trans (abs_nonneg _) (h j)

-- dominance is closed under sums
theorem CoeffDom.add {P Q A B : ℝ[X]} (hP : CoeffDom P A) (hQ : CoeffDom Q B) :
    CoeffDom (P + Q) (A + B) := fun j => by
  rw [coeff_add, coeff_add]
  exact le_trans (abs_add_le _ _) (add_le_add (hP j) (hQ j))

-- the sign of a coefficient does not matter
theorem CoeffDom.neg {P A : ℝ[X]} (h : CoeffDom P A) : CoeffDom (-P) A := fun j => by
  rw [coeff_neg, abs_neg]
  exact h j

-- dominance is closed under products
theorem CoeffDom.mul {P Q A B : ℝ[X]} (hP : CoeffDom P A) (hQ : CoeffDom Q B) :
    CoeffDom (P * Q) (A * B) := fun j => by
  rw [coeff_mul, coeff_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hP _) (hQ _) (abs_nonneg _) ((hP.nonneg _))

-- dominance is closed under the derivative
theorem CoeffDom.derivative {P A : ℝ[X]} (h : CoeffDom P A) :
    CoeffDom (derivative P) (derivative A) := fun j => by
  rw [coeff_derivative, coeff_derivative, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ j + 1)]
  exact mul_le_mul_of_nonneg_right (h _) (by positivity)


-- =======================================  MAIN THEOREM  ======================================= --

-- a polynomial with nonnegative coefficients increases on `[0, ∞)`
theorem CoeffDom.eval_mono {A : ℝ[X]} (h : CoeffDom A A) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    A.eval a ≤ A.eval b := by
  rw [eval_eq_sum_range, eval_eq_sum_range]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _)
    (h.nonneg j)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
