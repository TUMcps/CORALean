module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat
public import CORALean.Global.Float.NoNaN

@[expose] public section

/-!
# `reachFloatChecked`, without a NaN

`reachFloat` followed by `checkNoNaN`: `none` where it is `none` or a float of its result is
a NaN. A `some` is the unchecked `some` (`reachFloatChecked_eq_some`), so whatever is proved
of `reachFloat` holds of it, and the NaN test that the trust base asks of the caller has
been made.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input zonotope
* `params` – reachability parameters
* `options` – reachability options

## Output
* the unchecked result, or none if a float is NaN
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloat`, or `none` if a float of its result is a NaN. -/
def NeurNetContrSys.reachFloatChecked (sys : NeurNetContrSys (LinearSys 𝕋 n) 𝒵[𝕋] n)
    (U_ext : Zonotope (Vec 𝕋 sys.nExt)) (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℕ)
    (options : NeurNetContrSys.ReachOptions 𝕋) :
    Option (Zonotope (Vec 𝕋 n)) :=
  ifNoNaN (𝕋 := 𝕋) (sys.reachFloat U_ext params options)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
