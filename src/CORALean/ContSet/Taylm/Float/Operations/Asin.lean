module

public import CORALean.ContSet.Taylm.Float.Operations.Taylor
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.ArcsinCoef
public import CORALean.ContSet.Taylm.Float.Operations.ArcsinBound
public import CORALean.Global.Float.InverseTrig

@[expose] public section

/-!
# `Taylm.asin`

The exact layer's `asin` with every number enclosed: the zeroth coefficient `arcsin c` between
`asinDown` and `asinUp`, the others `Taylm.arcsinCoef`, the Lagrange bound `Taylm.arcsinBound` at
the magnitude `Taylm.magUp`. `p` and `q` are the precisions of `asinDown`/`asinUp` and
`Global/Float/Sqrt`.
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

def Taylm.asin (p q : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let c := T.constCoef
  T.taylor c
    (fun k => match k with
      | 0 => asinDown p q c
      | j + 1 => (Taylm.arcsinCoef q c j).inf)
    (fun k => match k with
      | 0 => asinUp p q c
      | j + 1 => (Taylm.arcsinCoef q c j).sup)
    (Taylm.arcsinBound q T.magUp T.maxOrder)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
