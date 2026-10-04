import CORALean.ContSet.Zoo.Float.Zoo
import CORALean.ContSet.Taylm.Float.Operations.Rdivide
import CORALean.ContSet.Interval.Float.Operations.Rdivide

/-!
# `Zoo.rdivide`, over a floating-point scalar

As `plus`, with `Taylm.rdivide` and `Interval.rdivide`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.rdivide (Z₁ Z₂ : Zoo 𝕋 n) : Zoo 𝕋 n :=
  ⟨Option.map₂ Taylm.rdivide Z₁.taylm Z₂.taylm, Option.map₂ Interval.rdivide Z₁.ivl Z₂.ivl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
