module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# `MatExp.scaleConj` commutes with the exponential

`S⁻¹ e^X S = e^{S⁻¹ X S}`, Mathlib's `Matrix.exp_conj` at the unit `S⁻¹ = diag (1/s)`: the
exponential of a matrix read in balanced coordinates is the exponential of the balanced matrix.

## Inputs
* `s` – scales
* `X` – matrix

## Hypotheses
* `hs` – no scale is zero

## Conclusion
* the similarity of the exponential is the exponential of the similarity
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.scaleConj_exp {s : Fin n → ℝ} (hs : ∀ i, s i ≠ 0) (X : Mat ℝ n n) : -- --- CONCL ---
    MatExp.scaleConj s (exp X) = exp (MatExp.scaleConj s X) := by -- --- PROOF ---
  have hinv : (diagonal fun i => (s i)⁻¹)⁻¹ = diagonal s := by
    refine Matrix.inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (hs i))
  have hu : IsUnit (diagonal fun i => (s i)⁻¹) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (hs i)).isUnit
  unfold MatExp.scaleConj
  have h := Matrix.exp_conj (diagonal fun i => (s i)⁻¹) X hu
  rw [hinv] at h
  exact h.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
