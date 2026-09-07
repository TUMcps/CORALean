import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpMulti

/-!
# `PolyZonotope.relaxExpGreedy`

The exact layer's loop, over this layer's sets. Nothing here rounds: the loop
only sequences `relaxExpMulti`, and every rounding a relaxation makes is already
charged to the box by the step it makes it in.

That is why the two layers' loops are the same recursion rather than one refining
the other. What differs is what a selection can be — a machine scalar has the
decidable order and equality that reading edge weights off the exponent matrix
needs, where ℝ has neither — and the selection is a parameter, so that difference
never reaches this file.

The box grows once per step, so the number of steps is what a caller trades
precision against here, as much as which pairs the selection picks.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Merge at whatever the selection names, at most `n` times. -/
def PolyZonotope.relaxExpGreedy
    (sel : (pZ : PolyZonotope 𝕋 n) →
      Option ((d : ℕ) × (Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)))) :
    ℕ → PolyZonotope 𝕋 n → PolyZonotope 𝕋 n
  | 0, pZ => pZ
  | m + 1, pZ =>
    (sel pZ).elim pZ fun sp => PolyZonotope.relaxExpGreedy sel m (pZ.relaxExpMulti sp.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
