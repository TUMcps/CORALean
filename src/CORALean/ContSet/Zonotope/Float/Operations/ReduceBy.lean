module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `Zonotope.reduceBy`

CORA's reduction at a given partition, unchanged in shape and sound for every
one of them. Nothing is charged to the box: the centre and kept generators are
copied exactly, and the diagonal block rounds *up*, which only enlarges.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's reduction at a given partition, unchanged in shape and sound for
every one of them. Nothing is charged to the box: the centre and kept generators
are copied exactly, and the diagonal block rounds *up*, which only enlarges. -/
def Zonotope.reduceBy (Z : Zonotope (Vec 𝕋 n)) (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    Zonotope (Vec 𝕋 n) where
  h := q + n
  c := Z.c
  G := Fin.append (fun l => Z.G (part.left l))
         (diagonalBlock (radius fun i l => Z.G (part.right l) i))
  I_error := Z.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
