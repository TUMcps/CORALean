module

public import CORALean.ContSet.Taylm.Float.Operations.Taylor
public import CORALean.ContSet.Taylm.Float.Operations.SqrtCoef
public import CORALean.ContSet.Taylm.Float.Operations.SqrtBound

@[expose] public section

/-!
# `Taylm.sqrt`

The exact layer's `sqrt` with every number enclosed: the coefficients `Taylm.sqrtCoef` at the
center, the Lagrange bound `Taylm.sqrtBound` at the smaller of the center and the bottom of the
range, where `√⁽ᴺ⁺¹⁾` is largest. `q` is the precision of the square root.

## Inputs
* `q` – precision of the square root
* `T` – Taylor model

## Output
* Taylor model of the square root of the argument
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.sqrt (q : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  T.taylor T.constCoef (fun k => (Taylm.sqrtCoef q T.constCoef k).inf)
    (fun k => (Taylm.sqrtCoef q T.constCoef k).sup)
    (Taylm.sqrtBound q (minimum T.constCoef T.bounds.inf) T.maxOrder)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
