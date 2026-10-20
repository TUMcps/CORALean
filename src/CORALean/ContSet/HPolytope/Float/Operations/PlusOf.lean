module

public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.ContSet.Float.Operations.SupportBound

@[expose] public section

/-!
# `HPolytope.plusOf`

What a float halfspace description cannot do exactly: the caller names
directions and the bounds are composed, `addUp` when two extents are added.

## Inputs
* `Aq` – `q × n` matrix

## Hypotheses
* `u₁` – a float bound of `P₁.construct` along each row
* `u₂` – a float bound of `P₂.construct` along each row

## Output
* the polytope on the directions `Aq` bounded by the added bounds of `u₁` and `u₂`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}
variable {P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.plusOf (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.construct (rowLin Aq i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.construct (rowLin Aq i)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.ofBounds Aq fun i => (u₁ i).add (u₂ i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
