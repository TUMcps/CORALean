module

public import CORALean.ContSet.Zoo.Float.Zoo
public import CORALean.ContSet.Taylm.Float.Operations.Times
public import CORALean.ContSet.Interval.Float.Operations.Times

@[expose] public section

/-!
# `Zoo.times`, over a floating-point scalar

As `plus`, with `Taylm.times` and `Interval.times`.
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

def Zoo.times (Z₁ Z₂ : Zoo 𝕋 n) : Zoo 𝕋 n :=
  ⟨Option.map₂ Taylm.times Z₁.taylm Z₂.taylm, Option.map₂ Interval.times Z₁.ivl Z₂.ivl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
