import CORALean.ContSet.PolyZonotope.Real.Operations.DropRadius

/-!
# `PolyZonotope.reduceBy`

Split out of `Reduce.lean` (issue #62): read again by the float layer's own
`reduceBy`, by `reduceGirard` and `reduceGirardDependent` in this directory, and
by `Theorems/ReduceByOuter.lean`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- Partitions both generator blocks rather than choosing either: what
`partD.left` and `partI.left` name is kept, with the former's exponent columns,
and the rest is absorbed into a diagonal block of `n` independent generators. -/
def PolyZonotope.reduceBy (PZ : PolyZonotope (Vec ℝ n)) {d r dI rI : ℕ}
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) : PolyZonotope (Vec ℝ n) where
  p := PZ.p
  h := d
  q := dI + n
  c := PZ.c
  G := fun l => PZ.G (partD.left l)
  E := fun k l => PZ.E k (partD.left l)
  GI := Fin.append (fun j => PZ.GI (partI.left j))
          (Matrix.diagonal (PZ.dropRadius partD partI))

end CORALean.Real
