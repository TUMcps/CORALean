module

public import CORALean.ContDynamics.LinearSys.Operations.ReachAdaptiveFloatChecked

@[expose] public section

/-!
# A checked `reachAdaptiveFloat` that returns a result returns the unchecked one

`reachAdaptiveFloatChecked` is `reachAdaptiveFloat` followed by `checkNoNaN`, so a `some` of
it is the unchecked `some`, and none of its floats is a NaN. Whatever is proved of
`reachAdaptiveFloat` is proved of the checked result, which has passed the NaN test as well.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachAdaptiveFloatChecked_eq_some (sys : LinearSys 𝕋 n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.AdaptiveOptions 𝕋)
    {Rs : (List (LinearSys.AdaptiveStepInfo 𝕋 n))}
    (h : sys.reachAdaptiveFloatChecked params options = some Rs) :
    sys.reachAdaptiveFloat params options = some Rs ∧
      noNaN (𝕋 := 𝕋) (Rs.map fun r => (r.Δt, r.R)) = true := by -- --- PROOF ---
  unfold LinearSys.reachAdaptiveFloatChecked at h
  cases hr : sys.reachAdaptiveFloat params options with
  | none => simp [hr] at h
  | some infos =>
    rw [hr] at h
    simp only [Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨rfl, (ifNoNaN_eq_some hx).2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
