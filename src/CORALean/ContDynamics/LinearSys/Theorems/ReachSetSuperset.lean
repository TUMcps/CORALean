module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero

@[expose] public section

/-!
# A witness in `inputReach` is a witness in `reachSet`

The `⊇` half of `reachSet T R₀ U t = e^{tA} R₀ ⊕ inputReach U t`: every
point the closed form names is reached by the `Trajectory` the closed
form itself is — `closedForm_flow` and `closedForm_continuousOn` supplying its
`flow` and `cont` fields verbatim. A measurable, merely bounded input is
admissible, so a point named this way is genuinely reached.
`ReachSetSubset` is the other half.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point `e^{tA} R₀ ⊕ inputReach U t` names is `x t` for the
`Trajectory` that is `closedForm`'s own formula at the witnessing
input, `closedForm_flow` supplying exactly its `flow` field. -/
theorem LinearSys.mulVecLin_image_add_inputReach_subset_reachSet
    (sys : LinearSys 𝕋 n) (R₀ U : S n) {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) :
    (exp (t • toRealMat sys.A)).mulVecLin '' construct R₀ + sys.inputReach U t
      ⊆ sys.reachSet (Set.Icc 0 t) R₀ U t := by -- --- PROOF ---
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
