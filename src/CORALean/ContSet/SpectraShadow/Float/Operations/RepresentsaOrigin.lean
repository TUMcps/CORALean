import CORALean.ContSet.SpectraShadow.Float.Operations.RepresentsaPoint

/-!
# `SpectraShadow.representsa_origin`, over a floating-point scalar

CORA's `representsa_(SpS, 'origin')`: every axis support `0`, in a positive dimension. Here the
certified singleton test (`SpectraShadow.representsa_point`) at a box whose corners are `0`
(`le` both ways). Sufficient only.
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

def SpectraShadow.representsa_origin (S : SpectraShadow 𝕋 (Vec 𝕋 n))
    (Yup Ylo : Fin n → Mat 𝕋 S.k S.k)
    (β : Vec 𝕋 S.m) : Bool :=
  S.representsa_point Yup Ylo β &&
    match S.interval Yup Ylo with
    | some I => (List.finRange n).all fun i => le (I.sup i) zero && le zero (I.sup i)
    | none => false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
