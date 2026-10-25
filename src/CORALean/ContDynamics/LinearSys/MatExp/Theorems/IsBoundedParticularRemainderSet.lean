module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularRemainderSet

@[expose] public section

/-!
# `particularRemainderSet` is bounded

`isBounded_particularRemainderSet`: [1]'s `e^{At_i} E(Δt,η) Δt U` is bounded whenever `U` is,
which is what `err` needs of it to be the enclosing radius rather than a junk value.

## Inputs
* `A` – system matrix
* `ti` – step start time
* `U` – input set
* `Δt` – step length
* `η` – Taylor order

## Hypotheses
* `hU` – input set bounded

## Conclusion
* the particular remainder set is bounded

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Sonnet 5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{At_i} E(Δt,η) Δt U` is bounded whenever `U` is, which is what `err` needs of it to be
the enclosing radius rather than a junk value. -/
theorem MatExp.isBounded_particularRemainderSet (A : Mat ℝ n n) (ti : ℝ)
    {U : Set (Vec ℝ n)} (hU : Bornology.IsBounded U) (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    Bornology.IsBounded (MatExp.particularRemainderSet A ti U Δt η) := by -- --- PROOF ---
  refine isBounded_iff_forall_norm_le.mpr ⟨(∑ i, ‖(fun j => (exp (ti • A)) i j)‖₂)
    * ((n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U), fun y hy => ?_⟩
  -- the supremum norm is under the Euclidean one, coordinate by coordinate
  have hsup : ‖y‖ ≤ ‖y‖₂ :=
    (pi_norm_le_iff_of_nonneg (norm₂_nonneg y)).mpr fun i =>
      (Real.norm_eq_abs (y i)).trans_le (abs_le_norm₂ y i)
  exact hsup.trans (MatExp.norm₂_le_of_mem_particularRemainderSet A ti hU Δt η y hy)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
