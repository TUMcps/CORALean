import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Polynomials dominated coefficientwise

`P ≼ A` when `|aⱼ| ≤ bⱼ` for every coefficient. Dominance survives sums, products and
derivatives, and gives `|P y| ≤ A |y|`: the way to bound a polynomial that a recursion
built, from the recursion run on absolute values of its coefficients. It is what bounds
the high derivatives of `tanh`, `tan`, `atan`, `asin` and `acos`, each a polynomial in a
variable whose range is known.
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

-- dominance is closed under a nonnegative scalar
theorem CoeffDom.smul_nat {P A : ℝ[X]} (h : CoeffDom P A) (m : ℝ) (hm : 0 ≤ m) :
    CoeffDom (C m * P) (C m * A) := fun j => by
  rw [coeff_C_mul, coeff_C_mul, abs_mul, abs_of_nonneg hm]
  exact mul_le_mul_of_nonneg_left (h j) hm

-- dominance is closed under the factor `X`
theorem CoeffDom.X_mul {P A : ℝ[X]} (h : CoeffDom P A) : CoeffDom (X * P) (X * A) :=
  (show CoeffDom X X from fun j => by
    rw [coeff_X]; split_ifs <;> simp).mul h

-- the value at `y` is bounded by the dominating polynomial at `|y|`
theorem CoeffDom.of_abs_le {P A : ℝ[X]} (h : CoeffDom P A) (y : ℝ) :
    |P.eval y| ≤ A.eval |y| := by -- --- PROOF ---
  have hdeg : P.natDegree ≤ A.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    -- `A.coeff j = 0` for `j > A.natDegree`, hence `|P.coeff j| ≤ 0`
    have hA : A.coeff j = 0 := coeff_eq_zero_of_natDegree_lt hj
    exact abs_nonpos_iff.1 (hA ▸ h j)
  rw [eval_eq_sum_range' (n := A.natDegree + 1) (by omega),
    eval_eq_sum_range' (n := A.natDegree + 1) (by omega)]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_mul (h j) (le_refl _) (by positivity) (h.nonneg j)

-- a dominating polynomial dominates itself
theorem CoeffDom.self_of_dom {P A : ℝ[X]} (h : CoeffDom P A) : CoeffDom A A := fun j => by
  rw [abs_of_nonneg (h.nonneg j)]

-- a polynomial with nonnegative coefficients increases on `[0, ∞)`
theorem CoeffDom.eval_mono {A : ℝ[X]} (h : CoeffDom A A) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    A.eval a ≤ A.eval b := by
  rw [eval_eq_sum_range, eval_eq_sum_range]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _)
    (h.nonneg j)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The bound the file is for: a dominated polynomial at a point of magnitude at most `m`. -/
-- the two combined: at most the dominating polynomial at the magnitude
theorem CoeffDom.abs_eval_le {P A : ℝ[X]} (h : CoeffDom P A) {y m : ℝ} (hy : |y| ≤ m) :
    |P.eval y| ≤ A.eval m :=
  le_trans (h.of_abs_le y) (h.self_of_dom.eval_mono (abs_nonneg _) hy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
