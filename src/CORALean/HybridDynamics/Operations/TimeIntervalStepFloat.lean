import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat
import CORALean.HybridDynamics.Definitions.Location

/-!
# `Location.timeIntervalStepFloat`

`Location.timeIntervalStep` computed in `𝕋`: a location whose states are float
zonotopes encloses a stay of length up to `r` by its dynamics'
`timeIntervalStepFloat`. The input's contribution is named by the caller, as
for the exact step; `timeIntervalStepSplitFloat` computes it.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enclosure of a stay of length up to `r`, at Taylor order `η`. -/
def Location.timeIntervalStepFloat (ℓ : Location (Zonotope 𝕋) G L 𝕋 n) (r : 𝕋) (η : ℕ)
    (X₀ : Zonotope 𝕋 n) : Zonotope 𝕋 n :=
  ℓ.dynamics.timeIntervalStepFloat r η X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
