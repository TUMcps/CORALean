module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.DecayProductFloat
public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# The decay product covers `|γτ| t^k/k!` times the norm

The running product `acc_j = acc_{j-1} |h| t / j` rounded up stays above the exact
`a Π|h| t^k / k!`, the factor of [1, Thm. 3]'s bound that decays with the order: multiplying by
a nonnegative factor and dividing by `max(1, ⌊j⌋)`, which is at most `j`, never lowers an upper
bound.

## Inputs
* `wn` – norm bound
* `t` – time
* `H` – Hessenberg entries
* `a` – lower bound of the norm
* `k` – order

## Hypotheses
* `ha0` – lower bound nonnegative
* `ha` – lower bound below the norm bound
* `ht` – time nonnegative

## Conclusion
* the exact product is at most the float one

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.decayProduct_bound (wn t : 𝕋) (H : ℕ → ℕ → 𝕋) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a ≤ toReal wn) (ht : 0 ≤ toReal t) (k : ℕ) : -- --- CONCL ---
    a * (∏ j ∈ Finset.range k, |toReal (H (j + 1) j)|) * toReal t ^ k / (k.factorial : ℝ) ≤
      toReal (Krylov.decayProductFloat wn t H k) := by -- --- PROOF ---
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, mul_one, Krylov.decayProductFloat]
    exact ha
  | succ k ih =>
    set P : ℝ := a * (∏ j ∈ Finset.range k, |toReal (H (j + 1) j)|) * toReal t ^ k /
      (k.factorial : ℝ) with hP
    have hP0 : 0 ≤ P := by
      have : 0 ≤ ∏ j ∈ Finset.range k, |toReal (H (j + 1) j)| :=
        Finset.prod_nonneg fun j _ => abs_nonneg _
      positivity
    set acc := Krylov.decayProductFloat wn t H k with hacc
    have hh : 0 ≤ |toReal (H (k + 1) k)| := abs_nonneg _
    -- the numerator
    have h1 : P * |toReal (H (k + 1) k)| ≤ toReal (mulUp acc (absolute (H (k + 1) k))) := by
      refine le_trans ?_ (mul_le_mulUp _ _)
      rw [toReal_absolute]
      exact mul_le_mul_of_nonneg_right ih hh
    have h2 : P * |toReal (H (k + 1) k)| * toReal t ≤
        toReal (mulUp (mulUp acc (absolute (H (k + 1) k))) t) :=
      le_trans (mul_le_mul_of_nonneg_right h1 ht) (mul_le_mulUp _ _)
    -- the divisor, at least one and at most `k + 1`
    have hd1 : (1 : ℝ) ≤ toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) := by
      rw [toReal_maximum, toReal_one]; exact le_max_left _ _
    have hd2 : toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) ≤ ((k + 1 : ℕ) : ℝ) := by
      rw [toReal_maximum, toReal_one]
      refine max_le (by exact_mod_cast Nat.succ_pos k) ?_
      have := nsmulDown_le (k + 1) (one : 𝕋)
      rwa [toReal_one, mul_one] at this
    have hnum : 0 ≤ P * |toReal (H (k + 1) k)| * toReal t := by positivity
    -- the factorial and the product split off their last factor
    have heq : a * (∏ j ∈ Finset.range (k + 1), |toReal (H (j + 1) j)|) * toReal t ^ (k + 1) /
        ((k + 1).factorial : ℝ) = P * |toReal (H (k + 1) k)| * toReal t / ((k + 1 : ℕ) : ℝ) := by
      rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, hP]
      have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      have h' : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [heq]
    refine le_trans ?_ (div_le_divUp _ _ (by linarith))
    calc P * |toReal (H (k + 1) k)| * toReal t / ((k + 1 : ℕ) : ℝ)
        ≤ P * |toReal (H (k + 1) k)| * toReal t /
            toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) :=
          div_le_div_of_nonneg_left hnum (by linarith) hd2
      _ ≤ _ := div_le_div_of_nonneg_right h2 (by linarith)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
