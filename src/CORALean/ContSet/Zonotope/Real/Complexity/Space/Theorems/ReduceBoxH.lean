module

public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

@[expose] public section

/-!
# `Zonotope.reduceBox_h`

`reduceBox`'s generator count, exactly: `n` where the reduction actually drops generators, the
origin's `0` where it does not — the condition `reduceBox` itself branches on. `reduceByBox` fixes
its `h` at `n` regardless of how many generators it absorbs, which keeps this exact rather than a
bound: one absorbing generator per output *coordinate*, not per generator it replaces.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* result has `n` or no generators, by order
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `h` count of `reduceBox`'s result. -/
theorem Zonotope.reduceBox_h (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    (Z.reduceBox o).h = if o * n < Z.h then n else 0 := by
  unfold Zonotope.reduceBox
  split_ifs <;> rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
