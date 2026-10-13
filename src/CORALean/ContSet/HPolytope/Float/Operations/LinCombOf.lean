module

public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.ContSet.Float.Operations.SupportBound

@[expose] public section

/-!
# `HPolytope.linCombOf`

What a float halfspace description cannot do exactly: the caller names
directions and the bounds are composed, by segments between the two.
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

def HPolytope.linCombOf (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.construct (rowLin Aq i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.construct (rowLin Aq i)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.ofBounds Aq fun i => (u₁ i).segments (u₂ i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
