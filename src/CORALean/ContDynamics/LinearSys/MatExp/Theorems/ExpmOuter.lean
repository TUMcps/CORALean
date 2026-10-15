module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.Expm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpmTermsMem
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExponentialRemainderOuter

@[expose] public section

/-!
# `MatExp.expm` encloses the exponential of every member

`e^M` is the Taylor sum of order `η` plus its remainder: the sum is in `expmTerms`
(`expmTerms_mem`) and the remainder in `exponentialRemainder` (`exponentialRemainder_outer`).
Proved for `η ≥ 2` and `r ≠ 0`, where the series splits as written; CORA also runs smaller orders,
with `H` and `E` overlapping.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- For a nonzero step and order `η ≥ 2`, `expm` encloses `e^M` for every `M` in the box. -/
theorem MatExp.expm_outer (A : Interval (Mat ℝ n n)) {r : ℝ} (hr : r ≠ 0) {η : ℕ}
    (hη : 2 ≤ η) {M : Mat ℝ n n} (hM : M ∈ A.construct) :
    exp M ∈ (MatExp.expm A r η).construct := by -- --- PROOF ---
  obtain ⟨k, rfl⟩ : ∃ k, η = k + 2 := ⟨η - 2, by omega⟩
  have key : exp M = MatExp.expTaylor M (k + 2) + (exp M - MatExp.expTaylor M (k + 2)) := by
    abel
  rw [key]
  exact Interval.plus_outer _ _ (Set.add_mem_add (MatExp.expmTerms_mem A hr k hM)
    (MatExp.exponentialRemainder_outer A (k + 2) hM))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
