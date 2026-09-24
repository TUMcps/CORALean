import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

/-!
# The remainder bound vanishes as the order grows

[1]: adaptive reachability tunes the truncation order against an admissible
error, which rests on this: for a fixed `x`, `expRemainderBound x η → 0` as
`η → ∞`. The power term vanishes by Mathlib's `Real.summable_pow_div_factorial`,
`xⁿ/n! → 0`; the geometric factor tends to `1` as its numerator's share of the
denominator shrinks.

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

/-- Any admissible error is reachable by raising the truncation order: the
guarantee adaptive order selection rests on. -/
theorem MatExp.tendsto_expRemainderBound_atTop (x : Mat ℝ n n) :
    Tendsto (fun η : ℕ => MatExp.expRemainderBound x η) atTop (𝓝 0) := by -- --- PROOF ---
  have h1 : Tendsto (fun η : ℕ => ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) atTop (𝓝 0) :=
    (Real.summable_pow_div_factorial ‖x‖).tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
  have hden : Tendsto (fun η : ℕ => (η : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun η : ℕ => ‖x‖ / ((η : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have h3 : Tendsto (fun η : ℕ => (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹) atTop (𝓝 1) := by
    have := (tendsto_const_nhds.sub h2).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa using this
  simpa [MatExp.expRemainderBound] using h1.mul h3

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
