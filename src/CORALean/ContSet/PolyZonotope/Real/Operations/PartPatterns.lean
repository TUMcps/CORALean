module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.PartPattern
public import Mathlib.Data.List.Dedup

@[expose] public section

/-!
# `PolyZonotope.partPatterns`

The distinct exponent patterns in the factors `V`, each at the place of its last occurrence
(`List.dedup`; CORA's `unique(eM_v','rows','stable')` keeps the first).

## Inputs
* `pZ` – polynomial zonotope
* `V` – selected factors

## Output
* duplicate-free exponent patterns on those factors
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The distinct patterns of the generators, each at the place of its last occurrence
(`List.dedup`; CORA's `unique(..., 'stable')` keeps the first). -/
def PolyZonotope.partPatterns (pZ : PolyZonotope α) (V : Finset (Fin pZ.p)) :
    List (Fin pZ.p → ℕ) :=
  (List.ofFn (pZ.partPattern V)).dedup

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
