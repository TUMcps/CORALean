module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral

@[expose] public section

/-!
# `∫₀ʳ e^{0·s} ds` against `r I`

For the zero matrix only the zeroth term of the series `∑ᵢ Aⁱ r^{i+1}/(i+1)!` survives, so
`MatExp.expIntegral 0 r = r I`: with `A = 0` the system holds its state and a constant input `u`
moves it by `r u`.

## Inputs
* `r` – time

## Hypotheses
* none

## Conclusion
* the integral of the zero matrix's exponential is the time times the identity
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expIntegral_zero (r : ℝ) :
    MatExp.expIntegral (0 : Mat ℝ n n) r = r • (1 : Mat ℝ n n) := by
  unfold MatExp.expIntegral
  rw [tsum_eq_single 0 fun i hi => by simp [zero_pow hi]]
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
