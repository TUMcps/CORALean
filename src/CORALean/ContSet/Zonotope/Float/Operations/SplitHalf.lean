module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.CenterResidual

@[expose] public section

/-!
# `Zonotope.splitHalf`, over a floating-point scalar

One half of `Zonotope.split`: the center moved by the vector `s`, the `j`-th generator halved
(exact in a binary format), and the rounding of the new center paid into the error box through
`centerResidual`. The two halves of `split` are this at `∓ g_j/2`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.splitHalf (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) (s : Vec 𝕋 n) :
    Zonotope (Vec 𝕋 n) where
  h := Z.h
  c := fun i => addDown (Z.c i) (s i)
  G := Function.update Z.G j fun i => half (Z.G j i)
  I_error := Z.I_error.plus (Zonotope.centerResidual Z.c s)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
