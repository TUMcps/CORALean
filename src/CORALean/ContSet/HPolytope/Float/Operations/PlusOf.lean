import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
import CORALean.ContSet.ContSet.Float.SupportBound

/-!
# `HPolytope.plusOf`

What a float halfspace description cannot do exactly: the caller names
directions and the bounds are composed, `addUp` when two extents are added.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}
variable {P₁ P₂ : HPolytope 𝕋 n}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.plusOf (Aq : Mat 𝕋 q n)
    (u₁ : ∀ i, FloatBound 𝕋 P₁.construct (rowLin Aq i))
    (u₂ : ∀ i, FloatBound 𝕋 P₂.construct (rowLin Aq i)) : HPolytope 𝕋 n :=
  HPolytope.ofBounds Aq fun i => (u₁ i).add (u₂ i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
