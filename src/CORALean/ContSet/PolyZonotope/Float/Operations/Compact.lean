import CORALean.ContSet.PolyZonotope.Float.Operations.CompactFactors
import CORALean.ContSet.PolyZonotope.Float.Operations.CompactGens

/-!
# `PolyZonotope.compact`

The exact layer's `compact`, with the obstacles traded. The zero test on a
merged generator is simply not made here, costing a column that denotes nothing
rather than soundness; what appears instead is arithmetic, since merging two
columns adds their entries and a directed sum owes an error box.

Which columns survive is decided structurally: one per class, the least index
carrying that exponent column, which is `Real.PolyZonotope.rep` — `repKeep` is
its fixed points, and `card` of it is the monomial count `reduce` wanted.

Both directions of each fibre sum are computed (`fiberDown`/`fiberUp`), the
lower stored and the gap charged as a `generatorError`, the coefficient being a
monomial. `compactFactors` changes `p` and the exponent matrix and nothing
else, all over ℕ, so its nominal part is literally the exact layer's.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `compact`: merge, then drop the factors that fell out of use. -/
def PolyZonotope.compact (pZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n :=
  pZ.compactGens.compactFactors

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
