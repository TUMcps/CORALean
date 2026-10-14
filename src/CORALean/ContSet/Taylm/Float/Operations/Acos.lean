module

public import CORALean.ContSet.Taylm.Float.Operations.Taylor
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.ArcsinCoef
public import CORALean.ContSet.Taylm.Float.Operations.ArcsinBound
public import CORALean.Global.Float.InverseTrig

@[expose] public section

/-!
# `Taylm.acos`

The exact layer's `acos` with every number enclosed: the zeroth coefficient `arccos c` between
`acosDown` and `acosUp`, the others the negated `Taylm.arcsinCoef` (`arccos' = -arcsin'`), the
Lagrange bound `Taylm.arcsinBound` at the magnitude `Taylm.magUp`, the same as `arcsin`'s. `p` and
`q` are the precisions of `acosDown`/`acosUp` and `Global/Float/Sqrt`.
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

def Taylm.acos (p q : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let c := T.constCoef
  T.taylor c
    (fun k => match k with
      | 0 => acosDown p q c
      | j + 1 => neg (Taylm.arcsinCoef q c j).sup)
    (fun k => match k with
      | 0 => acosUp p q c
      | j + 1 => neg (Taylm.arcsinCoef q c j).inf)
    (Taylm.arcsinBound q T.magUp T.maxOrder)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
