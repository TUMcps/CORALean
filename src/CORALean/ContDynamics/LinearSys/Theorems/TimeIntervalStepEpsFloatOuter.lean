import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SideConditionOfLeFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepEpsFloat
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepFloatOuter

/-!
# `timeIntervalStepEpsFloat` holds the flow over the step

The order `MatExp.tuneOrder` returns passed `orderTest`, whose first half is the float
side condition `nrm ≤ (η + 2)/2`, and it is at least `2`: so it is admissible for the float
enclosures (`OrderAdmissibleFloat`), and `timeIntervalStepFloat_outer` applies at it.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of `X₀` under the flow, at every time of the step, is in the result. -/
theorem LinearSys.timeIntervalStepEpsFloat_outer (sys : LinearSys 𝕋 n) {r ε : 𝕋} {fuel : ℕ}
    {X₀ R : Zonotope (Vec 𝕋 n)} (hr : 0 < toReal r)
    (h : sys.timeIntervalStepEpsFloat r ε fuel X₀ = some R)
    {x : Vec ℝ n} (hx : x ∈ X₀.construct) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ toReal r) :
    exp (s • Scalar.toRealMat sys.A) *ᵥ x ∈ R.construct := by -- --- PROOF ---
  simp only [LinearSys.timeIntervalStepEpsFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨η, hη, rfl⟩ := h
  -- what the search's test certified, read back
  have htest := List.find?_some hη
  obtain ⟨k, -, hk⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hη)
  rw [MatExp.orderTest, Bool.and_eq_true] at htest
  have hadm : sys.OrderAdmissibleFloat r r η := ⟨by omega, MatExp.sideCondition_of_le htest.1⟩
  exact sys.timeIntervalStepFloat_outer hr hadm X₀ hx hs0 hs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
