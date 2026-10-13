import CORALean.ContSet.PolyZonotope.Float.Operations.DropRadius

/-!
# `PolyZonotope.reduceBy`

Split out of `Reduce.lean` (issue #62): read again by `reduceGirard` and
`reduceGirardDependent` in this directory and by `Theorems/ReduceByOuter.lean`,
all outside this file.

CORA's reduction at a given pair of partitions, sound for every one of them:
kept dependent generators keep their exponent columns, kept independent ones
are copied, and the rest becomes a box no longer tied to the factors.
`reduceBy` charges nothing to the error box beyond it: the centre and the kept
generators are copied exactly, and the diagonal block rounds *up* — twice,
once per block radius and once for their sum — which only enlarges an
over-approximation.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d r dI rI : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.reduceBy (pZ : PolyZonotope (Vec 𝕋 n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := d
  q := dI + n
  c := pZ.c
  G := fun l => pZ.G (partD.left l)
  E := fun k l => pZ.E k (partD.left l)
  GI := Fin.append (fun j => pZ.GI (partI.left j))
    fun j i => diagonalBlock (pZ.dropRadius partD partI) i j
  err := pZ.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
