module

public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat
public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# `Location.timeIntervalStepFloat`

`Location.timeIntervalStep` computed in `𝕋`: a location whose states are float
zonotopes encloses a stay of length up to `r` by its dynamics'
`timeIntervalStepFloat`. The input's contribution is named by the caller, as
for the exact step; `timeIntervalStepSplitFloat` computes it.

## Inputs
* `ℓ` – float location
* `r` – time step
* `η` – Taylor order
* `X₀` – initial zonotope

## Output
* float time-interval zonotope of the stay
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enclosure of a stay of length up to `r`, at Taylor order `η`. -/
def Location.timeIntervalStepFloat (ℓ : Location 𝒵[𝕋] G L 𝕋 n)
    (r : 𝕋) (η : ℕ)
    (X₀ : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  ℓ.dynamics.timeIntervalStepFloat r η X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
