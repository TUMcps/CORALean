module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.HomogeneousRemainderError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeOfMemSum

@[expose] public section

/-!
# A member of `F_u(Δt,η)` is entrywise bounded

`abs_entry_le_of_mem_inputCorrectionSet`: [1]'s `F_u(Δt,η)`, entrywise within its Taylor
terms' reach plus `|Δt|·‖E(Δt,η)‖`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
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

/-- A member of `F_u(Δt,η)` is entrywise within its Taylor terms' reach plus `|Δt|·‖E(Δt,η)‖`. -/
theorem MatExp.abs_entry_le_of_mem_inputCorrectionSet {A : Mat ℝ n n} {Δt : ℝ} {η : ℕ}
    {M : Mat ℝ n n} (hM : M ∈ MatExp.inputCorrectionSet A Δt η) (i j : Fin n) : -- --- CONCL ---
    |M i j| ≤ (∑ k ∈ Finset.Icc 2 (η + 1), |MatExp.corrCoeff k * Δt ^ k|
        * |((((Nat.factorial k : ℝ))⁻¹ • A ^ (k - 1)) : Mat ℝ n n) i j|)
      + |Δt| * ‖MatExp.expRemainderMat A Δt η‖ := by -- --- PROOF ---
  obtain ⟨Ms, hMs, _, ⟨ME, hME, rfl⟩, rfl⟩ := Set.mem_add.mp hM
  have hs := MatExp.abs_entry_le_of_mem_sum (Finset.Icc 2 (η + 1))
    (fun k => MatExp.corrCoeff k * Δt ^ k) (fun k => ((Nat.factorial k : ℝ))⁻¹ • A ^ (k - 1))
    hMs i j
  -- the scaled remainder block's entry is `|Δt|` times one under `E`'s norm
  have hE : |(Δt • ME) i j| ≤ |Δt| * ‖MatExp.expRemainderMat A Δt η‖ := by
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (((hME i j).trans (le_abs_self _)).trans (abs_entry_le_norm _ i j)) (abs_nonneg _)
  rw [Matrix.add_apply]
  exact (abs_add_le _ _).trans (add_le_add hs hE)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
