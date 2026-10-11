import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

/-!
# `rep` read off a table, over a floating-point scalar

`rep` costs a scan of every exponent column, and the merges ask for it once per
summand of every fibre of every entry. Computed once into an `Array`, the same
answers cost a lookup (issue #61).
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {p h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Real.PolyZonotope.rep E` at every column, in column order, so that a caller
which reads it many times pays for it once. A bare `Array` rather than a
function, so that a `let` shares it. -/
def PolyZonotope.repTab (E : Fin p → Fin h → ℕ) : Array (Fin h) :=
  ((List.finRange h).map (Real.PolyZonotope.rep E)).toArray

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
