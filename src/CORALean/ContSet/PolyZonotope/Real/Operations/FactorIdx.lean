module

public import CORALean.ContSet.PolyZonotope.Real.Operations.UsedFactors
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# The kept factors, indexed by a plain count

Split out of `Compact.lean` (issue #62): used again by `Theorems/
CompactFactorsExact.lean`, and reused unchanged by `ConPolyZono.factorIdx`,
both outside this file.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `k` – used factor number

## Output
* the original index of that used factor
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The kept factors, indexed by a plain count, as `compactIdx` does for
columns. -/
def PolyZonotope.factorIdx {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (k : Fin (PolyZonotope.usedFactors E).card) : Fin p :=
  (PolyZonotope.usedFactors E).orderIsoOfFin rfl k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
