import CORALean.ContDynamics.LinearSys.MatExp.Enclosures

/-!
# Shortening the step drives the remainder bound to zero

The counterpart of `tendsto_expRemainderBound_atTop`, which raises the order at
a fixed argument: here the order is fixed and the argument shrinks, which is
what a step selection varies.

The bound is a product, and the two factors go different ways: the numerator
`‖rA‖^{η+1}/(η+1)!` vanishes with the step, while the geometric factor tends to
`1` — it is not small, it is merely bounded, and the side condition is what
keeps it so.

`tendsto_mul_expRemainderBound_zero` is this with the step in front, which is
the shape `inputRemainder`'s radius has.
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

/-- The remainder bound vanishes as the step does, at a fixed order. -/
theorem MatExp.tendsto_expRemainderBound_zero (A : Mat ℝ n n) (η : ℕ) :
    Tendsto (fun r : ℝ => MatExp.expRemainderBound (r • A) η)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by -- --- PROOF ---
  have hnorm : Tendsto (fun r : ℝ => ‖r • A‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have heq : (fun r : ℝ => ‖r • A‖) = fun r => |r| * ‖A‖ := by
      funext r
      rw [norm_smul, Real.norm_eq_abs]
    rw [heq]
    have h : Tendsto (fun r : ℝ => |r|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h.mul_const ‖A‖
  -- the numerator vanishes with the step
  have h1 : Tendsto (fun r : ℝ => ‖r • A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hnorm.pow (η + 1)).div_const (Nat.factorial (η + 1) : ℝ)
    simpa [zero_pow (Nat.succ_ne_zero η)] using h
  -- the geometric factor is merely bounded, and tends to one
  have h2 : Tendsto (fun r : ℝ => (1 - ‖r • A‖ / ((η : ℝ) + 2))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hden : Tendsto (fun r : ℝ => ‖r • A‖ / ((η : ℝ) + 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hnorm.div_const ((η : ℝ) + 2)
    have h := (tendsto_const_nhds.sub hden).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa using h
  simpa [MatExp.expRemainderBound] using h1.mul h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
