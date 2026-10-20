module

public import CORALean.ContSet.ConPolyZono.Real.Operations.DropRadius

@[expose] public section

/-!
# `ConPolyZono.reduceBy`

Partitions both generator blocks: what `partD.left` and `partI.left` name is
kept, with the former's exponent columns, and the rest is absorbed into a
diagonal block of `n` independent generators. The constraints stand.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `partD` – split of the dependent generators
* `partI` – split of the independent generators

## Output
* enclosure keeping the chosen generators
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n d r dI rI : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Partitions both generator blocks: what `partD.left` and `partI.left` name is
kept, with the former's exponent columns, and the rest is absorbed into a
diagonal block of `n` independent generators. The constraints stand. -/
def ConPolyZono.reduceBy (cPZ : ConPolyZono (Vec ℝ n))
    (partD : Split (Fin cPZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin cPZ.qI) into (Fin dI) ⊕ (Fin rI)) : ConPolyZono (Vec ℝ n) where
  p := cPZ.p
  h := d
  qI := dI + n
  c := cPZ.c
  G := fun l => cPZ.G (partD.left l)
  E := fun k l => cPZ.E k (partD.left l)
  GI := Fin.append (fun j => cPZ.GI (partI.left j))
          (Matrix.diagonal (cPZ.dropRadius partD partI))
  cons := cPZ.cons
  cons_eq := cPZ.cons_eq
  cons_dom := cPZ.cons_dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
