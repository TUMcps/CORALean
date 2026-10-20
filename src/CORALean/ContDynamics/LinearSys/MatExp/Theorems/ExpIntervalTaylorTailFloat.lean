module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorTailFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InvFactorialBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# `expIntervalTaylorTail` holds orders three to `κ` of every member, over a float

Induction on `κ`, as `Real.MatExp.taylorTail_mem_expIntervalTaylorTail` does: below order three
the sum is empty and the tail is the zero point, and from three on the top order peels off,
`smul_outer` at `invFactorialBounds`'s two facts and `matPow_outer` enclosing it.

## Inputs
* `B` – float interval matrix
* `N` – member matrix
* `κ` – Taylor order

## Hypotheses
* `hN` – member lies in the interval matrix

## Conclusion
* orders three and up of the member lie in the float interval tail
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored zero matrix is the point `0`. -/
theorem aux_zero_mem_point :
    (0 : Mat ℝ n n) ∈ (Interval.point (α := Mat 𝕋 n n) fun _ _ => zero).construct := by
  have h : toRealMat (fun _ _ => zero : Mat 𝕋 n n) = 0 := by
    funext i j; simp [toRealMat, toReal_zero]
  rw [← h]
  exact Interval.mem_point (α := Mat 𝕋 n n) fun _ _ => zero


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.taylorTail_mem_expIntervalTaylorTail (B : Interval (Mat 𝕋 n n))
    {N : Mat ℝ n n} (hN : N ∈ B.construct) (κ : ℕ) : -- --- CONCL ---
    (∑ i ∈ Finset.Ico 3 (κ + 1), ((Nat.factorial i : ℝ)⁻¹) • N ^ i)
      ∈ (MatExp.expIntervalTaylorTail B κ).construct := by -- --- PROOF ---
  induction κ with
  | zero =>
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact aux_zero_mem_point
  | succ k ih =>
    -- below order three the range is empty; from three on the top order peels off
    match k, ih with
    | 0, _ =>
      rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      exact aux_zero_mem_point
    | 1, _ =>
      rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      exact aux_zero_mem_point
    | m + 2, ih =>
      rw [Finset.sum_Ico_succ_top (by omega),
        add_comm (∑ i ∈ Finset.Ico 3 (m + 2 + 1), ((Nat.factorial i : ℝ)⁻¹) • N ^ i)
          (((Nat.factorial (m + 2 + 1) : ℝ))⁻¹ • N ^ (m + 2 + 1))]
      show _ ∈ (Interval.matPlus _
        (MatExp.expIntervalTaylorTail B (m + 2))).materialiseMat.construct
      rw [Interval.materialiseMat_eq]
      exact Interval.matPlus_outer _ _
        (Interval.smul_outer (MatExp.invFactorialBounds_mem (m + 3)).1
          (MatExp.invFactorialBounds_mem (m + 3)).2 (Interval.matPow B (m + 3))
          (Interval.matPow_outer B hN (m + 3))) ih

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
