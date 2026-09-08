import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoMulExpRemainderBoundZero

/-!
# Any admissible error is reachable, in the step

[1]: the ε-form of `tendsto_mul_expRemainderBound_zero`, and the statement
adaptive step selection actually calls: for every admissible error there is a
positive step whose contribution beats it, and whose side condition
`‖r • A‖/(η+2) < 1` also holds, so the `r` produced names a real bound.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The step the tuning algorithm actually needs to name: a real bound under
`ε`, sound because its own side condition holds too. -/
theorem MatExp.exists_mul_expRemainderBound_lt (A : Mat ℝ n n) (η : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r * MatExp.expRemainderBound (r • A) η < ε ∧
      ‖r • A‖ / ((η : ℝ) + 2) < 1 := by -- --- PROOF ---
  have hev1 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r * MatExp.expRemainderBound (r • A) η < ε :=
    (MatExp.tendsto_mul_expRemainderBound_zero A η).eventually_lt_const hε
  have hnorm : Tendsto (fun r : ℝ => ‖r • A‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have heq : (fun r : ℝ => ‖r • A‖) = fun r => |r| * ‖A‖ := by
      funext r; rw [norm_smul, Real.norm_eq_abs]
    rw [heq]
    have h : Tendsto (fun r : ℝ => |r|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h.mul_const ‖A‖
  have hT2 : Tendsto (fun r : ℝ => ‖r • A‖ / ((η : ℝ) + 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hnorm.div_const ((η : ℝ) + 2)
  have hev2 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ‖r • A‖ / ((η : ℝ) + 2) < 1 :=
    hT2.eventually_lt_const one_pos
  have hev3 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (0 : ℝ) < r := self_mem_nhdsWithin
  obtain ⟨r, ⟨hr1, hr2⟩, hr3⟩ := ((hev1.and hev2).and hev3).exists
  exact ⟨r, hr3, hr1, hr2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
