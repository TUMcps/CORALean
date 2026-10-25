module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.HomogeneousRemainderError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeOfMemSum

@[expose] public section

/-!
# A member of `F_x(Δt,η)` is entrywise bounded

`abs_entry_le_of_mem_stateCorrectionSet`: [1]'s `F_x(Δt,η)`, entrywise within its Taylor
terms' reach plus `‖E(Δt,η)‖`.

## Inputs
* `A` – system matrix
* `Δt` – step length
* `η` – Taylor order
* `M` – member matrix
* `i` – row index
* `j` – column index

## Hypotheses
* `hM` – member of the state correction set

## Conclusion
* the entry is bounded by its Taylor terms and the remainder norm

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

/-- A member of `F_x(Δt,η)` is entrywise within its Taylor terms' reach plus `‖E(Δt,η)‖`. -/
theorem MatExp.abs_entry_le_of_mem_stateCorrectionSet {A : Mat ℝ n n} {Δt : ℝ} {η : ℕ}
    {M : Mat ℝ n n} (hM : M ∈ MatExp.stateCorrectionSet A Δt η) (i j : Fin n) : -- --- CONCL ---
    |M i j| ≤ (∑ k ∈ Finset.Icc 2 η, |MatExp.corrCoeff k * Δt ^ k|
        * |((((Nat.factorial k : ℝ))⁻¹ • A ^ k) : Mat ℝ n n) i j|)
      + ‖MatExp.expRemainderMat A Δt η‖ := by -- --- PROOF ---
  obtain ⟨Ms, hMs, ME, hME, rfl⟩ := Set.mem_add.mp hM
  have hs := MatExp.abs_entry_le_of_mem_sum (Finset.Icc 2 η) (fun k => MatExp.corrCoeff k * Δt ^ k)
    (fun k => ((Nat.factorial k : ℝ))⁻¹ • A ^ k) hMs i j
  -- the remainder block's entry is under `E`'s, hence under its norm
  have hE : |ME i j| ≤ ‖MatExp.expRemainderMat A Δt η‖ :=
    ((hME i j).trans (le_abs_self _)).trans (abs_entry_le_norm _ i j)
  rw [Matrix.add_apply]
  exact (abs_add_le _ _).trans (add_le_add hs hE)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
