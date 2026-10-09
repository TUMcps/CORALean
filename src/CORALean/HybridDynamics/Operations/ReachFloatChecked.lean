import CORALean.HybridDynamics.Operations.ReachFloat
import CORALean.Global.Float.NoNaN

/-!
# `reachFloatChecked`, without a NaN

`reachFloat` followed by `checkNoNaN`: `none` where it is `none` or a float of its result is
a NaN. A `some` is the unchecked `some` (`reachFloatChecked_eq_some`), so whatever is proved
of `reachFloat` holds of it, and the NaN test that the trust base asks of the caller has
been made.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloat`, or `none` if a float of its result is a NaN. The locations carry no floats. -/
def HybridAutomaton.reachFloatChecked (HA : HybridAutomaton (Zonotope 𝕋) (HPolytope 𝕋) L 𝕋 n)
    (tFinal : ℚ) (options : LinearSys.ReachOptions 𝕋) (K : ℕ) (ℓ : L) (X₀ : Zonotope 𝕋 n) :
    Option (List (L × Zonotope 𝕋 n)) :=
  checkNoNaN (𝕋 := 𝕋) (HA.reachFloat tFinal options K ℓ X₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
