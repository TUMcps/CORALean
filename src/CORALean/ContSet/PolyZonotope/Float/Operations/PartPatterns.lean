module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.partPatterns`, over a floating-point scalar

The distinct exponent patterns of the generators in the factors `V`, first appearance first: the
grouping of CORA's `partZonotope`. It reads the exponent matrix only, which holds naturals.

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

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The distinct patterns of the generators, first appearance first. -/
def PolyZonotope.partPatterns (pZ : PolyZonotope (Vec 𝕋 n)) (V : Finset (Fin pZ.p)) :
    List (Fin pZ.p → ℕ) :=
  (List.ofFn fun i : Fin pZ.h => fun k => if k ∈ V then pZ.E k i else 0).dedup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
