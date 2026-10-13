import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

/-!
# `affineDynamicsError`'s explicit bound

`affineDynamicsErrorBound`: an explicit `Δt`-polynomial dominating `affineDynamicsError`, so
[1, Lemma 3]'s asymptotics reduce to that bound's, a real-valued computation.

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

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `Δt`-polynomial dominating `affineDynamicsError`. -/
noncomputable def MatExp.affineDynamicsErrorBound (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : ℝ :=
  4 * (n : ℝ) * ((Real.exp (Δt * ‖A‖) - 1 - Δt * ‖A‖ + MatExp.expRemainderBound (Δt • A) η)
        * (∑ j, H.absBound j)
      + (Δt * (Real.exp (Δt * ‖A‖) - 1) + Δt * MatExp.expRemainderBound (Δt • A) η)
        * (∑ j, |ũ j|))
    + Real.sqrt H.h * ((n : ℝ) * (Δt * ‖A‖ * Real.exp (Δt * ‖A‖)) * ∑ l, ∑ j, |H.G l j|)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
