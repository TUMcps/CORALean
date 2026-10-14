module

public import CORALean.ContSet.Zoo.Float.Zoo
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Zoo.plus`, over a floating-point scalar

Members combined as in the exact layer: the float Taylor models by `Taylm.plus`, the intervals by
`Interval.plus`, kept where both zoos have them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.plus (Z₁ Z₂ : Zoo 𝕋 n) : Zoo 𝕋 n :=
  ⟨Option.map₂ Taylm.plus Z₁.taylm Z₂.taylm, Option.map₂ Interval.plus Z₁.ivl Z₂.ivl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
