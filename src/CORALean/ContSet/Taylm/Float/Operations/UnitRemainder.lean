module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.Global.Float.DivFact

@[expose] public section

/-!
# `Taylm.unitRemainder`

The Lagrange bound `Bᴺ⁺¹ / (N+1)!` of an expansion at the constant part whose `(N+1)`-th
derivative is at most one in magnitude, as for `sin` and `cos`: `B` the reach of the range
hull from the center, rounded up, and the product rounded up.

## Inputs
* `T` – Taylor model

## Output
* Lagrange bound for derivatives of magnitude at most one
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
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
  let B := maximum zero (maximum (subUp b.sup c) (subUp c b.inf))      -- |f t - c| ≤ B on the box
  mulUp (powUp B (N + 1)) (divFact ⟨one, one⟩ (N + 1)).sup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
