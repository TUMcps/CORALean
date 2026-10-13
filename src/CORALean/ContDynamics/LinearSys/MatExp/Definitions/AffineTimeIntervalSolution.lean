module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# `H(τ_k)`, the exact tube

`affineTimeIntervalSolution`: [1, Prop. 1]'s exact time-interval solution `H(τ_k)` of the
affine dynamics `ẋ = Ax + ũ`, over the elapsed times `[0,Δt]` of the step.

[1] writes the tube's flow map `e^{At}` at absolute time `t ∈ τ_k = [t_k,t_{k+1}]` while every
other set in the display is relative to `t_k`; read literally the two do not compose, so the
elapsed time `t - t_k ∈ [0,Δt]` is what this definition runs over.

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

/-- [1, Prop. 1]'s exact time-interval solution `H(τ_k)` of the affine dynamics `ẋ = Ax + ũ`,
over the elapsed times `[0,Δt]` of the step. -/
noncomputable def MatExp.affineTimeIntervalSolution (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) : Set (Vec ℝ n) :=
  {y | ∃ t ∈ Set.Icc (0:ℝ) Δt, ∃ x ∈ H.construct,
    y = (exp (t • A)).mulVec x + (MatExp.expIntegral A t).mulVec ũ}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
