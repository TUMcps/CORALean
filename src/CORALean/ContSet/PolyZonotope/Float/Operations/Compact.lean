module

public import CORALean.ContSet.PolyZonotope.Float.Operations.CompactFactors
public import CORALean.ContSet.PolyZonotope.Float.Operations.CompactGens

@[expose] public section

/-!
# `PolyZonotope.compact`

The exact layer's `compact`, with the obstacles traded. The zero test on a merged generator is
not made here, costing a column that denotes nothing rather than soundness; merging two columns
adds their entries, and a directed sum owes an error box. Which columns survive is structural:
the least index carrying each exponent column (`Real.PolyZonotope.rep`; `repKeep` is its fixed
points). Both directions of each fibre sum are computed (`fiberDown`/`fiberUp`), the lower
stored and the gap charged as a `generatorError`.

## Inputs
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope with merged generators and dropped unused factors
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `compact`: merge, then drop the factors that fell out of use. -/
def PolyZonotope.compact (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  pZ.compactGens.compactFactors

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
