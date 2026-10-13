import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionAgree

/-!
# The exact layer's tolerance the stored agreement rows amount to

What is left of the stored agreement interval once the centre difference the
rows also carry is subtracted. The two error boxes already fit inside it, which
is the whole argument for `intersection`'s soundness.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.intersectionD (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Real.Interval (Vec ℝ n) :=
  ⟨fun i => toReal ((ConPolyZono.intersectionAgree cPZ₁ cPZ₂).inf i)
      - (toReal (cPZ₂.c i) - toReal (cPZ₁.c i)),
   fun i => toReal ((ConPolyZono.intersectionAgree cPZ₁ cPZ₂).sup i)
      - (toReal (cPZ₂.c i) - toReal (cPZ₁.c i))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
