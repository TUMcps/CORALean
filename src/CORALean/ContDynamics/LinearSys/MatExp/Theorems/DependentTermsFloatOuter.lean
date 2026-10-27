module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.DependentTermsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalWFloat
public import CORALean.ContSet.Interval.Float.Theorems.ExactSquareOuter
public import CORALean.ContSet.Interval.Float.Theorems.IntervalMatrixOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.DependentTermsOuter

@[expose] public section

/-!
# `MatExp.dependentTerms` contains the exact terms of every member

For a member `M` of the box, `M * M` lies in `exactSquare`, scaled by `r²` it lies in the scaled
box (the scalar is bracketed by `mulDown r r` and `mulUp r r`), and the rebuild from center and
radius contains that box. The second output is `I + W(r)`, where `W(r)` is in `expIntervalW` and
the identity is the point box.

## Inputs
* `A` – interval matrix
* `r` – step length
* `M` – member matrix

## Hypotheses
* `hM` – `M` lies in the interval matrix

## Conclusion
* the exact terms of the member lie in the dependent terms
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.dependentTerms_outer (A : Interval (Mat 𝕋 n n)) (r : 𝕋) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) : -- --- CONCL ---
    toReal r ^ 2 • (M * M) ∈ (MatExp.dependentTerms A r).intSq.construct ∧
      1 + Real.MatExp.expW M (toReal r) ∈
        (MatExp.dependentTerms A r).intH.construct := by -- --- PROOF ---
  -- the squared step is bracketed by the directed products
  have hlo : toReal (mulDown r r) ≤ toReal r ^ 2 := by
    rw [sq]; exact mulDown_le_mul r r
  have hhi : toReal r ^ 2 ≤ toReal (mulUp r r) := by
    rw [sq]; exact mul_le_mulUp r r
  -- the identity is the zeroth power
  have h1 : (1 : Mat ℝ n n) ∈ (Interval.point (diagonalBlock fun _ => (one : 𝕋))).construct := by
    have h := Interval.matPow_outer A hM 0
    rw [pow_zero] at h
    exact h
  refine ⟨Interval.intervalMatrix_outer _
      (Interval.smul_outer hlo hhi _ (Interval.exactSquare_outer A hM)),
    Interval.intervalMatrix_outer _
      (Interval.matPlus_outer _ _ h1 (MatExp.expW_mem_expIntervalW A r hM))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
