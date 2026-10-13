module

public import CORALean.HybridDynamics.Operations.LinearResetSynchronize
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `LinearReset.synchronize` applies to the sum

The synchronized affine reset at a point is the sum of the component resets there, plus the
pre-jump value at the coordinates `idStates`: exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearReset.synchronize_apply (W : Fin k → Mat ℝ n n) (w : Fin k → Vec ℝ n)
    (idStates : Finset (Fin n)) (x : Vec ℝ n) (i : Fin n) :
    ((LinearReset.synchronize W w idStates).1 *ᵥ x + (LinearReset.synchronize W w idStates).2) i =
      (if i ∈ idStates then x i else 0) + ∑ j, (W j *ᵥ x + w j) i := by -- --- PROOF ---
  -- the sum of matrices acts as the sum of their actions
  have hsum : (∑ j, W j) *ᵥ x = ∑ j, W j *ᵥ x := by
    exact Matrix.sum_mulVec _ _ _
  simp only [LinearReset.synchronize, Pi.add_apply, add_mulVec, hsum, mulVec_diagonal,
    Finset.sum_apply]
  -- regroup the three summands
  rw [Finset.sum_add_distrib]
  split_ifs
  · simp; ring
  · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
