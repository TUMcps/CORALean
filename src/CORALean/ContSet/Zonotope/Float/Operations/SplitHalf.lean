import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.CenterResidual

/-!
# `Zonotope.splitHalf`, over a floating-point scalar

One half of `Zonotope.split`: the centre moved by the vector `s`, the `j`-th generator halved
(exact in a binary format), and the rounding of the new centre paid into the error box through
`centerResidual`. The two halves of `split` are this at `∓ g_j/2`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.splitHalf (Z : Zonotope 𝕋 n) (j : Fin Z.h) (s : Vec 𝕋 n) : Zonotope 𝕋 n where
  h := Z.h
  c := fun i => addDown (Z.c i) (s i)
  G := fun i => Function.update (Z.G i) j (half (Z.G i j))
  E := Z.E.plus (Zonotope.centerResidual Z.c s)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
