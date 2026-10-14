module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError

@[expose] public section

/-!
# `Zonotope.reduceAndAbsorbBy`

`reduceBy` and `absorbError` in one pass, and the reason to prefer it.

Each alone ends in a diagonal block, and two merge into one with summed radii,
since per coordinate they are independent. Doing both therefore costs the `q + n`
generators `reduceBy` alone would; run separately they cost `q + n + n`. What
remains in the box is only what the rounded centre shift owes.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.reduceAndAbsorbBy (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Zonotope (Vec 𝕋 n) where
  h := q + n
  c := Z.shiftDown
  G := Fin.append (fun l => Z.G (part.left l))
         (diagonalBlock fun i => addUp (radius (fun i l => Z.G (part.right l) i) i)
           (Z.errorRadius i))
  I_error := Interval.residual Z.shiftDown Z.shiftUp Z.shiftDown

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
