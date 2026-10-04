import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.partPatterns`, over a floating-point scalar

The distinct exponent patterns of the generators in the factors `V`, first appearance first: the
grouping of CORA's `partZonotope`. It reads the exponent matrix only, which holds naturals.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The distinct patterns of the generators, first appearance first. -/
def PolyZonotope.partPatterns (pZ : PolyZonotope 𝕋 n) (V : Finset (Fin pZ.p)) :
    List (Fin pZ.p → ℕ) :=
  (List.ofFn fun i : Fin pZ.h => fun k => if k ∈ V then pZ.E k i else 0).dedup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
