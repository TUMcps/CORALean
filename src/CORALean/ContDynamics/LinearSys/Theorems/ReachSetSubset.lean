import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Theorems.EqClosedFormOfFlow

/-!
# Every `Trajectory` run is a witness in `e^{tA} R₀ ⊕ inputReach U t`

The `⊆` half. `eq_closedForm_of_flow` does the work: the run `x` and
`closedForm (x 0) u` agree everywhere on `[0, t]`, so `x t` is exactly the point
the closed form, at the very input the run carries, names — and that point
splits into `e^{tA} (x 0)` and an `inputReach` witness by definition.

`init` enters nowhere in that argument, which is why the theorem it is stated
from takes no initial set: only here, to place `x 0` in `R₀`.
`ReachSetSuperset` is the other half.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-September-2026
-- Last update:   19-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point `reachSet` names is a closed-form point, so it is the
sum of a moved initial point and an `inputReach` witness. -/
theorem LinearSys.reachSet_subset_mulVecLin_image_add_inputReach
    (sys : LinearSys 𝕋 n) (R₀ U : S n) {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) :
    sys.reachSet (Set.Icc 0 t) R₀ U t
      ⊆ (exp (t • toRealMat sys.A)).mulVecLin '' construct R₀
        + sys.inputReach U t := by -- --- PROOF ---
  rintro _ ⟨x, u, traj, rfl⟩
  have hxt : x t = sys.closedForm (x 0) u t :=
    sys.eq_closedForm_of_flow ht hU traj.input traj.meas traj.cont traj.flow ⟨ht, le_rfl⟩
  rw [Set.mem_add]
  refine ⟨exp (t • toRealMat sys.A) *ᵥ x 0, ⟨x 0, traj.init, rfl⟩,
    ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s, ⟨u, traj.input, traj.meas, rfl⟩, ?_⟩
  rw [hxt]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
