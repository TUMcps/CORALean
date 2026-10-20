module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderBoundZero

@[expose] public section

/-!
# The input remainder's radius vanishes as the step shrinks

[1]: `inputRemainder A r η`'s radius is `r * expRemainderBound (r • A) η`; it
tends to `0` as `r → 0⁺`, the guarantee adaptive step selection rests on, the
other tuning knob besides the order. `‖r • A‖ = |r| * ‖A‖` reduces both factors
of the bound to elementary limits at `0`.

## Inputs
* `A` – system matrix
* `η` – Taylor order

## Hypotheses
* none

## Conclusion
* the step times the remainder bound tends to zero as the step shrinks

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa using hr.mul (MatExp.tendsto_expRemainderBound_zero A η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
