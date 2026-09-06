import CORALean.ContSet.ConPolyZono.Float.Operations.And
import CORALean.ContSet.ConPolyZono.Float.Operations.AndAgree

/-!
# The exact layer's tolerance the stored agreement rows amount to

What is left of the stored agreement interval once the centre difference the
rows also carry is subtracted. The two error boxes already fit inside it, which
is the whole argument for `and`'s soundness.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.andD (C₁ C₂ : ConPolyZono 𝕋 n) : Real.Interval (Vec ℝ n) :=
  ⟨fun i => toReal ((ConPolyZono.andAgree C₁ C₂).inf i)
      - (toReal (C₂.c i) - toReal (C₁.c i)),
   fun i => toReal ((ConPolyZono.andAgree C₁ C₂).sup i)
      - (toReal (C₂.c i) - toReal (C₁.c i))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
