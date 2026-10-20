module

public import CORALean.ContSet.PolyZonotope.Real.Operations.DropRadius

@[expose] public section

/-!
# `PolyZonotope.reduceBy`

Split out of `Reduce.lean` (issue #62): read again by the float layer's own
`reduceBy`, by `reduceGirard` and `reduceGirardDependent` in this directory, and
by `Theorems/ReduceByOuter.lean`, all outside this file.

## Inputs
* `pZ` – polynomial zonotope
* `d` – number of kept dependent generators
* `r` – number of dropped dependent generators
* `dI` – number of kept independent generators
* `rI` – number of dropped independent generators
* `partD` – split of the dependent generators
* `partI` – split of the independent generators

## Output
* polynomial zonotope with the split-off generators boxed
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Partitions both generator blocks rather than choosing either: what
`partD.left` and `partI.left` name is kept, with the former's exponent columns,
and the rest is absorbed into a diagonal block of `n` independent generators. -/
def PolyZonotope.reduceBy (pZ : PolyZonotope (Vec ℝ n)) {d r dI rI : ℕ}
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) : PolyZonotope (Vec ℝ n) where
  p := pZ.p
  h := d
  q := dI + n
  c := pZ.c
  G := fun l => pZ.G (partD.left l)
  E := fun k l => pZ.E k (partD.left l)
  GI := Fin.append (fun j => pZ.GI (partI.left j))
          (Matrix.diagonal (pZ.dropRadius partD partI))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
