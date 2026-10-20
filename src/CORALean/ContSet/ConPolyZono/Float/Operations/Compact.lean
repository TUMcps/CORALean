module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactCons
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactors
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGens
public import CORALean.ContSet.ConPolyZono.Float.Operations.Materialise

@[expose] public section

/-!
# `ConPolyZono.compact`

The exact layer's three stages, with the obstacles traded as for `PolyZonotope`: no zero test is
made, and which columns survive is decided structurally by `repKeep`. A merged *generator* column
is off by the gap between the two directed masked sums, paid into the ambient box; a merged
*constraint* column pays into the rows' slack `b_error`. Each stage is `materialise`d before the
next reads it (issue #61).

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* same set with equal columns merged and unused factors dropped
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
