import CORALean.ContSet.Taylm.Float.Operations.Taylor
import CORALean.ContSet.Taylm.Float.Operations.MagUp
import CORALean.ContSet.Taylm.Float.Operations.ArcsinCoef
import CORALean.ContSet.Taylm.Float.Operations.ArcsinBound
import CORALean.Global.Float.InverseTrig

/-!
# `Taylm.asin`

The exact layer's `asin` with every number enclosed: the zeroth coefficient `arcsin c` between
`asinDown` and `asinUp`, the others `Taylm.arcsinCoef`, the Lagrange bound `Taylm.arcsinBound` at
the magnitude `Taylm.magUp`. `p` and `q` are the precisions of `asinDown`/`asinUp` and
`Global/Float/Sqrt`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.asin (p q : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let c := T.constCoef
  T.taylor c
    (fun k => match k with
      | 0 => asinDown p q c
      | j + 1 => (Taylm.arcsinCoef q c j).1)
    (fun k => match k with
      | 0 => asinUp p q c
      | j + 1 => (Taylm.arcsinCoef q c j).2)
    (Taylm.arcsinBound q T.magUp T.maxOrder)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
