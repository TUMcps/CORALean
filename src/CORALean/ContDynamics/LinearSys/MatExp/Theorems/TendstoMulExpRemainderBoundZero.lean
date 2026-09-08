import CORALean.ContDynamics.LinearSys.MatExp.Enclosures

/-!
# The input remainder's radius vanishes as the step shrinks

[1]: `inputRemainder A r η`'s radius is `r * expRemainderBound (r • A) η`; it
tends to `0` as `r → 0⁺`, the guarantee adaptive step selection rests on, the
other tuning knob besides the order. `‖r • A‖ = |r| * ‖A‖` reduces both factors
of the bound to elementary limits at `0`.

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

/-- Any admissible error is reachable by shortening the step: the guarantee
adaptive step selection rests on. -/
theorem MatExp.tendsto_mul_expRemainderBound_zero (A : Mat ℝ n n) (η : ℕ) :
    Tendsto (fun r : ℝ => r * MatExp.expRemainderBound (r • A) η)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by -- --- PROOF ---
  have hnorm : Tendsto (fun r : ℝ => ‖r • A‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have heq : (fun r : ℝ => ‖r • A‖) = fun r => |r| * ‖A‖ := by
      funext r; rw [norm_smul, Real.norm_eq_abs]
    rw [heq]
    have h : Tendsto (fun r : ℝ => |r|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h.mul_const ‖A‖
  have h1 : Tendsto (fun r : ℝ => ‖r • A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (hnorm.pow (η + 1)).div_const (Nat.factorial (η + 1) : ℝ)
    simpa [zero_pow (Nat.succ_ne_zero η)] using this
  have h2 : Tendsto (fun r : ℝ => (1 - ‖r • A‖ / ((η : ℝ) + 2))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hden : Tendsto (fun r : ℝ => ‖r • A‖ / ((η : ℝ) + 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hnorm.div_const ((η : ℝ) + 2)
    have := (tendsto_const_nhds.sub hden).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa using this
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa [MatExp.expRemainderBound] using hr.mul (h1.mul h2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
