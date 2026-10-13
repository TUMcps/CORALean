import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

/-!
# `Zonotope.reduceBox_h`

`reduceBox`'s generator count, exactly: `n` where the reduction actually drops
generators, the origin's `0` where it does not — the same condition
`reduceBox` itself branches on, so the two sides of the `if` line up with the
two definitions it calls. `reduceByBox` fixes its `h` at `n` regardless of how
many generators it absorbs, which is what keeps this exact rather than a bound.

Not `k * n` for some count `k` of dropped generators: `reduceByBox` pays one
absorbing generator per output *coordinate*, not per generator it replaces, so
the box is `n` generators however many were dropped.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceBox_h (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    (Z.reduceBox o).h = if o * n < Z.h then n else 0 := by
  unfold Zonotope.reduceBox
  split_ifs <;> rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
