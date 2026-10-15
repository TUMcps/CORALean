module

public import CORALean.ContSet.SpectraShadow.Float.Theorems.DualBoundLe
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# A spectrahedral shadow's interval hull, over a floating-point scalar
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.interval (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Yup Ylo : Fin n → Mat 𝕋 S.k S.k) :
    Option (Interval (Vec 𝕋 n)) :=
  let unit : Fin n → Vec 𝕋 n := fun i r => if r = i then one else zero
  if (List.finRange n).all fun i =>
      S.dualCertified (unit i) (Yup i) && S.dualCertified (-unit i) (Ylo i) then
    some ⟨fun i => neg (S.dualBound (-unit i) (Ylo i)), fun i => S.dualBound (unit i) (Yup i)⟩
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
