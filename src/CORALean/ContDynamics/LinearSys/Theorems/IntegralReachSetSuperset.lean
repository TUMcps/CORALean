import CORALean.ContDynamics.LinearSys.Definitions.IntegralReachSet
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero

/-!
# A witness in `inputReach` is a witness in `integralReachSet`

The `⊇` half of `integralReachSet T R₀ U t = e^{tA} R₀ ⊕ inputReach U t`: every
point the closed form names is reached by the `IntegralTrajectory` the closed
form itself is — `closedForm_flow` and `closedForm_continuousOn` supplying its
`flow` and `cont` fields verbatim. This is the new content over
`ReachSetOuter`/`ReachSetSubsetReach`, which only place `Trajectory` runs
between enclosures — a measurable, merely-bounded input has no `Trajectory`
to appeal to. `IntegralReachSetSubset` is the other half.
-/

-- Authors:       Tobias Ladner
-- Written:       15-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point `e^{tA} R₀ ⊕ inputReach U t` names is `x t` for the
`IntegralTrajectory` that is `closedForm`'s own formula at the witnessing
input, `closedForm_flow` supplying exactly its `flow` field. -/
theorem LinearSys.mulVecLin_image_add_inputReach_subset_integralReachSet
    (sys : LinearSys 𝕋 n) (R₀ U : S n) {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) :
    (exp (t • toRealMat sys.A)).mulVecLin '' construct R₀ + sys.inputReach U t
      ⊆ sys.integralReachSet (Set.Icc 0 t) R₀ U t := by -- --- PROOF ---
  rintro y hy
  rw [Set.mem_add] at hy
  obtain ⟨_, ⟨r, hr, rfl⟩, w, ⟨u, hmem, hmeas, rfl⟩, rfl⟩ := hy
  -- `closedForm r u` is the run: `closedForm_flow`/`closedForm_continuousOn` give its fields
  refine ⟨sys.closedForm r u, u, ⟨?_, hmem, hmeas,
    sys.closedForm_continuousOn r ht hU hmem hmeas,
    fun τ hτ => sys.closedForm_flow r ht hU hmem hmeas hτ⟩, rfl⟩
  rw [sys.closedForm_zero r u]; exact hr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
