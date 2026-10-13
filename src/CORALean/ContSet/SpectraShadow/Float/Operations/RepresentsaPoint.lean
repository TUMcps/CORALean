module

public import CORALean.ContSet.Conversion.Float.SpectraShadow_to_Interval
public import CORALean.ContSet.SpectraShadow.Float.Operations.ContainsPoint

@[expose] public section

/-!
# `SpectraShadow.representsa_point`, over a floating-point scalar

CORA's `representsa_(SpS, 'point')`: a member whose coordinates are the support values from
above and from below. Here both are certificates checked by float tests: the certified interval
hull (`SpectraShadow.interval`, `2n` dual certificates) has `inf = sup` in every coordinate
(`le` both ways), and that corner is a member (`SpectraShadow.containsPoint` with the
certificate `β`). Then the set is that single point. Sufficient only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.representsa_point (S : SpectraShadow 𝕋 (Vec 𝕋 n))
    (Yup Ylo : Fin n → Mat 𝕋 S.k S.k)
    (β : Vec 𝕋 S.m) : Bool :=
  match S.interval Yup Ylo with
  | some I => ((List.finRange n).all fun i => le (I.inf i) (I.sup i) && le (I.sup i) (I.inf i))
      && S.containsPoint I.sup β
  | none => false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
