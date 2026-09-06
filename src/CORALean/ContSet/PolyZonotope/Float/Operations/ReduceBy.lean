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

def PolyZonotope.reduceBy (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := d
  q := dI + n
  c := PZ.c
  G := fun i l => PZ.G i (partD.left l)
  E := fun k l => PZ.E k (partD.left l)
  GI := fun i => Fin.append (fun j => PZ.GI i (partI.left j))
    (diagonalBlock (PZ.dropRadius partD partI) i)
  err := PZ.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
