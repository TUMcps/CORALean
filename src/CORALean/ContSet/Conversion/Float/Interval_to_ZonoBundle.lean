import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ZonoBundle

/-!
# A box as a bundle of one, over a floating-point scalar

Through the box's own zonotope, then `Zonotope.zonoBundle`, exact by
`Set.iInter_const`. All the loss is the box-to-zonotope step's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Interval.zonoBundle (I : Interval (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) := I.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.zonoBundle_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.zonoBundle.construct :=
  subset_trans I.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
