import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral

/-!
# `T = 1` for `A = 0` and `Δt = 1`

The propagation matrix `T = A⁻¹(e^{AΔt} - I)` of [1, Eq. 14-20], `MatExp.expIntegral`, is the
series `Σ_j Δt^{j+1} A^j/(j+1)!`; for `A = 0` it is `Δt`, here at `Δt = 1` in dimension `1`.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.expIntegral_zero_one : MatExp.expIntegral (0 : Mat ℝ 1 1) 1 = 1 := by -- --- PROOF ---
  unfold MatExp.expIntegral
  rw [tsum_eq_single 0]
  · simp
  · intro i hi
    simp [zero_pow hi]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
