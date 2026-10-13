module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# `Σᵢ Ãᵢ`, the correlated summand's single matrix

`particularCoeffSum`: `Σᵢ₌ᵢ₀^η Ãᵢ`: the single matrix [1]'s eq. (25)'s correlated summand
applies to `U0` once.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Σᵢ₌ᵢ₀^η Ãᵢ`: the single matrix [1]'s eq. (25)'s correlated summand applies to `U0` once. -/
noncomputable def MatExp.particularCoeffSum (A : Mat ℝ n n) (Δt : ℝ) (i0 η : ℕ) : Mat ℝ n n :=
  ∑ i ∈ Finset.Ico i0 (η + 1), MatExp.particularCoeff A Δt i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
