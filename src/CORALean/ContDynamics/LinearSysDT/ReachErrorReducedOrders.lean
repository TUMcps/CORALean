import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.Reduce
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

/-!
# `reachErrorOrders` with the error reduced at every step

`reachErrorReduced` at a per-step order sequence: the same recursion, one
`reduce` on top read at `o (k + 1)` in place of the one fixed `o`. The
direction is what keeps it sound at any sequence, exactly as for the fixed
order — the error stands on the right of `reach_subset_reachSet_add_error`, so
enlarging it keeps that inclusion regardless of which order enlarged it.

Otherwise the recursion of `reachErrorOrders` unchanged, and at the same
instances: `Zonotope` and `𝕋 = ℝ`.
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

/-- What `reachOrders` owes after `k` steps, reduced at every step: the same
recursion as `reachErrorOrders` with one `reduce` on top, at that step's own
order. -/
noncomputable def LinearSysDT.reachErrorReducedOrders (sys : LinearSysDT ℝ n) (o : ℕ → ℕ)
    (ho : ∀ k, 0 < o k) (R₀ U : Zonotope (Vec ℝ n)) : ℕ → Zonotope (Vec ℝ n)
  | 0 => Zonotope.ofPoint 0
  | k + 1 => Zonotope.reduce
      ((Zonotope.mtimes sys.A (sys.reachErrorReducedOrders o ho R₀ U k)).plus
        (Zonotope.reduceBox
          ((Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) o ho R₀ U k)).plus U) (o (k + 1))))
      (o (k + 1))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
