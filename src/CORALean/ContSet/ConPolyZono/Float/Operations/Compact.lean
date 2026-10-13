module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactCons
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactors
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGens

@[expose] public section

/-!
# `ConPolyZono.compact`

The exact layer's three stages, with the obstacles traded as they are for
`PolyZonotope`: no zero test is made, costing a column that denotes nothing
rather than soundness, and which columns survive is decided structurally by
`repKeep`, one per class. What appears instead is arithmetic, merging two
columns being an addition.

The two merges pay into different places, which is the whole of what the
constraints add. A merged *generator* column is off by the gap between the two
directed masked sums, and that gap is a `generatorError` in the ambient box, as
for `PolyZonotope`. A merged *constraint* column has no ambient box to pay into
— its rows live in `Fin m`, not in the state — so it pays into `b`.

Each stage is `materialise`d before the next reads it (issue #61): the stages
return closures over their input, so three stacked unstored stages made every
read of the result walk all of them again, and `reduce` then read the result
`O(h²)` times. `materialise_eq` makes it invisible to the theorems.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   11-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `compact`: the generators, then the constraints, then the factors
that fell out of use. -/
def ConPolyZono.compact (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  cPZ.compactGens.materialise.compactCons.materialise.compactFactors.materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
