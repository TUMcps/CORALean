import CORALean.ContSet.Taylm.Float.Operations.Taylor
import CORALean.ContSet.Taylm.Float.Operations.MagUp
import CORALean.ContSet.Taylm.Float.Operations.ArcsinCoef
import CORALean.ContSet.Taylm.Float.Operations.ArcsinBound
import CORALean.Global.Float.InverseTrig

/-!
# `Taylm.acos`

The exact layer's `acos` with every number enclosed: the zeroth coefficient `arccos c` between
`acosDown` and `acosUp`, the others the negated `Taylm.arcsinCoef` (`arccos' = -arcsin'`), the
Lagrange bound `Taylm.arcsinBound` at the magnitude `Taylm.magUp`, the same as `arcsin`'s. `p` and
`q` are the precisions of `acosDown`/`acosUp` and `Global/Float/Sqrt`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


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
      | j + 1 => neg (Taylm.arcsinCoef q c j).2)
    (fun k => match k with
      | 0 => acosUp p q c
      | j + 1 => neg (Taylm.arcsinCoef q c j).1)
    (Taylm.arcsinBound q T.magUp T.maxOrder)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
