module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetSuperset
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepInnerInner
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded

@[expose] public section

/-!
# A step's inner approximation lands in the exact reachable set

`timePointStepInner_inner` puts the step's inner approximation inside
`e^{Ar} X₀ ⊕ inputReach U r`, and that sum *is* the set the step's Carathéodory
runs reach (`reachSet_eq`): the integral equation admits every measurable input
`inputReach` quantifies over.

So nothing needs the derivative of `MatExp.expIntegral`: the held input the
inner approximation is built on is one admissible input, and its run is a
`IsTrajectory` by `closedForm_flow`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The step's end minus its own error ball is *contained in* the states the
system reaches at `t = r`. -/
theorem LinearSys.timePointStepInner_subset_reachSet (sys : LinearSys 𝕋 n) {r : ℝ}
    (hr : 0 < r) (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (X₀ U : Zonotope (Vec ℝ n)) :
    sys.timePointStepInner r η X₀ U ⊆ sys.reachSet (S := 𝒵) (Set.Icc 0 r) X₀ U r :=
  (sys.timePointStepInner_inner hr η hε X₀ U).trans
    (sys.mulVecLin_image_add_inputReach_subset_reachSet (S := 𝒵) X₀ U hr.le
      (Zonotope.isBounded_construct U))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
