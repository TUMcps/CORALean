import CORALean.HybridDynamics.Operations.LocationReachFloat
import CORALean.Global.Float.NoNaN

/-!
# `reachFloatChecked`, without a NaN

`reachFloat` followed by `checkNoNaN`: `none` where it is `none` or a float of its result is
a NaN. A `some` is the unchecked `some` (`reachFloatChecked_eq_some`), so whatever is proved
of `reachFloat` holds of it, and the NaN test that the trust base asks of the caller has
been made.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {G : ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloat`, or `none` if a float of its result is a NaN. -/
def Location.reachFloatChecked (ℓ : Location (Zonotope 𝕋) G L 𝕋 n) (tFinal : ℚ)
    (options : LinearSys.ReachOptions 𝕋) (X₀ : Zonotope 𝕋 n) :
    Option (List (Zonotope 𝕋 n)) :=
  checkNoNaN (𝕋 := 𝕋) (ℓ.reachFloat tFinal options X₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
