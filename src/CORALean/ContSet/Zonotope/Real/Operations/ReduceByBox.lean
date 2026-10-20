module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy

@[expose] public section

/-!
# `Zonotope.reduceByBox`

The error `reduceBy` pays, as a set of its own: the diagonal block it puts in place of the
dropped generators, centered at the origin. `reduceBy` is the kept generators plus this box, so
this is the `E` in `Ẑ ⊆ Z + E`. Centered at `0` and not at `Z.c`, which is why the reverse
inclusion holds: the dropped generators contribute `0` to `Z` at coefficient `0`, so the reduced
set never reaches further than `Z` plus this box. Not a `Reduce` operation and no class
instantiates it — a caller wanting an inner approximation asks for the box beside the reduction.

## Inputs
* `Z` – zonotope
* `part` – split of the generator indices

## Output
* box absorbing the dropped generators
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `reduceBy` absorbs the dropped generators into, on its own: one
entry per coordinate, the absorbed rows' `1`-norm, centered at the origin. -/
def Zonotope.reduceByBox (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Zonotope (Vec ℝ n) where
  h := n
  c := 0
  G := Matrix.diagonal fun i => ∑ l, |Z.G (part.right l) i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
