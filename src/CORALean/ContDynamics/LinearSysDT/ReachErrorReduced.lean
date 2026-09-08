import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.Reduce
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

/-!
# `reachError` with the error reduced at every step

`reachError` never reduces in its own recursion, so it gains a box per step and
holds `k * n` generators: past `k = o` the subtrahend is described by more
generators than the run it comes off, which is bounded at `o * n` throughout.

A `reduce` per step caps it, and the *direction* is what makes that sound. The
error stands on the right of `reach_subset_reachSet_add_error`, added to the
exact set, so enlarging it keeps that inclusion — the reverse of the usual
situation, where enlarging a computed set is what breaks a guarantee. And
`reduce_outer` enlarges. So the price is precision, never soundness: the error
is bigger, and `reachInnerReduced` is correspondingly smaller.

What it buys is `reachErrorReduced_h_le` — `o * n` at every horizon, `k = 0`
included, which is the run's own bound.

Otherwise the recursion of `reachError` unchanged, and at the same instances:
`Zonotope` and `𝕋 = ℝ`, `mtimes` being exact only there.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `reach` owes after `k` steps, reduced at every step: the same
recursion as `reachError` with one `reduce` on top, which enlarges it and so
keeps it sound where it is used. -/
noncomputable def LinearSysDT.reachErrorReduced (sys : LinearSysDT ℝ n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) : ℕ → Zonotope (Vec ℝ n)
  | 0 => Zonotope.ofPoint 0
  | k + 1 => Zonotope.reduce
      ((Zonotope.mtimes sys.A (sys.reachErrorReduced o ho R₀ U k)).plus
        (Zonotope.reduceBox
          ((Zonotope.mtimes sys.A (sys.reach (S := 𝒵) o ho R₀ U k)).plus U) o)) o

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
