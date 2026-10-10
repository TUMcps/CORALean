import CORALean.ContSet.Conversion.Float.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB
import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb

/-!
# `ConPolyZono.linComb`

CORA's `@conPolyZono/linComb`, as the exact layer lays it out: the float
`PolyZonotope.linComb` on the generators, which is where the fresh factor for the
segment parameter comes from and where every rounding is paid, with the two
constraint systems carried along side by side.

The constraint side computes nothing. `plusA` places the two matrices
block-diagonally with `zero` off the blocks, `plusB` concatenates, and the
exponent matrices are over ℕ, so the constraints of the result are exactly the
two operands' — read on the factors they came with, the fresh one at exponent
zero. The error box is therefore the generator part's, unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.linComb (cPZ₁ cPZ₂ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n :=
  let pZ := cPZ₁.polyZonotope.linComb cPZ₂.polyZonotope   -- the segment's generators
  { p := cPZ₁.p + cPZ₂.p + 1
    h := cPZ₁.h + cPZ₂.h + (cPZ₁.h + cPZ₂.h + 1)
    q := cPZ₁.q + cPZ₂.q
    m := cPZ₁.m + cPZ₂.m
    s := cPZ₁.s + cPZ₂.s
    c := pZ.c
    G := fun i l => pZ.G l i
    E := pZ.E
    GI := fun i j => pZ.GI j i
    A := ConPolyZono.plusA cPZ₁.A cPZ₂.A
    b := ConPolyZono.plusB cPZ₁.b cPZ₂.b
    EC := Real.ConPolyZono.padE (Real.PolyZonotope.plusE cPZ₁.EC cPZ₂.EC) 1
    err := pZ.err }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
