module

public import CORALean.ContDynamics.LinearSys.Operations.ReachAdaptiveFloat
public import CORALean.Global.Float.NoNaN

@[expose] public section

/-!
# `reachAdaptiveFloatChecked`, without a NaN

`reachAdaptiveFloat` followed by the NaN test: `none` where it is `none` or a float of its
result is a NaN. The floats of a step are its `Δt` and the set `R`; the rest is ℚ or ℕ.
A `some` is the unchecked `some` (`reachAdaptiveFloatChecked_eq_some`), so whatever is
proved of `reachAdaptiveFloat` holds of it, with the NaN test made.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachAdaptiveFloat`, or `none` if a float of its result is a NaN. -/
def LinearSys.reachAdaptiveFloatChecked (sys : LinearSys 𝕋 n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.AdaptiveOptions 𝕋) :
    Option (List (LinearSys.AdaptiveStepInfo 𝕋 n)) :=
  (sys.reachAdaptiveFloat params options).bind fun infos =>
    (ifNoNaN (𝕋 := 𝕋) (infos.map fun r => (r.Δt, r.R))).map fun _ => infos

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
