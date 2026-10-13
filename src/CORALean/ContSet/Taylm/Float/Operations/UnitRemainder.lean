module

public import CORALean.ContSet.Taylm.Float.Operations.ConstCoef
public import CORALean.ContSet.Taylm.Float.Operations.Bounds
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact

@[expose] public section

/-!
# `Taylm.unitRemainder`

The Lagrange bound `Bᴺ⁺¹ / (N+1)!` of an expansion at the constant part whose `(N+1)`-th
derivative is at most one in magnitude, as for `sin` and `cos`: `B` the reach of the range
hull from the centre, rounded up, and the product rounded up.
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

def Taylm.unitRemainder (T : Taylm 𝕋 n) : 𝕋 :=
  let N := T.maxOrder
  let c := T.constCoef
  let b := T.bounds
  let B := maximum zero (maximum (subUp b.2 c) (subUp c b.1))      -- |f t - c| ≤ B on the box
  mulUp (powUp B (N + 1)) (divFact (one, one) (N + 1)).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
