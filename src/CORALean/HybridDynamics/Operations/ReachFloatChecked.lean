module

public import CORALean.HybridDynamics.Operations.ReachFloat
public import CORALean.Global.Float.NoNaN

@[expose] public section

/-!
# `reachFloatChecked`, without a NaN

`reachFloat` followed by `checkNoNaN`: `none` where it is `none` or a float of its result is
a NaN. A `some` is the unchecked `some` (`reachFloatChecked_eq_some`), so whatever is proved
of `reachFloat` holds of it, and the NaN test that the trust base asks of the caller has
been made.

## Inputs
* `HA` – hybrid automaton
* `tFinal` – final time
* `options` – reach options
* `K` – jump depth
* `ℓ` – initial location
* `X₀` – initial zonotope

## Output
* location-tagged reach sets, none on failure or NaN
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloat`, or `none` if a float of its result is a NaN. The locations carry no floats. -/
def HybridAutomaton.reachFloatChecked
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (tFinal : ℚ) (options : LinearSys.ReachOptions 𝕋) (K : ℕ) (ℓ : L) (X₀ : Zonotope (Vec 𝕋 n)) :
    Option (List (L × Zonotope (Vec 𝕋 n))) :=
  checkNoNaN (𝕋 := 𝕋) (HA.reachFloat tFinal options K ℓ X₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
