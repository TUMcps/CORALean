module

public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpMulti

@[expose] public section

/-!
# `PolyZonotope.relaxExpGreedy`

The exact layer's loop, over this layer's sets. Nothing here rounds: the loop
only sequences `relaxExpMulti`, and every rounding a relaxation makes is already
charged to the box by the step it makes it in.

The two layers' loops are the same recursion; what differs is what a selection
can be (a machine scalar has the decidable order and equality that reading edge
weights needs, where ℝ has neither), and the selection is a parameter. The box
grows once per step, so the number of steps trades precision.

## Inputs
* `sel` – chooser of the next pair of generators

## Output
* function from step count and set to the greedily relaxed set
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Merge at whatever the selection names, at most `n` times. -/
def PolyZonotope.relaxExpGreedy
    (sel : (pZ : PolyZonotope (Vec 𝕋 n)) →
      Option ((d : ℕ) × (Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)))) :
    ℕ → PolyZonotope (Vec 𝕋 n) → PolyZonotope (Vec 𝕋 n)
  | 0, pZ => pZ
  | m + 1, pZ =>
    (sel pZ).elim pZ fun sp => PolyZonotope.relaxExpGreedy sel m (pZ.relaxExpMulti sp.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
