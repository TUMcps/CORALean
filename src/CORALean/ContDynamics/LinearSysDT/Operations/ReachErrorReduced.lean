module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

@[expose] public section

/-!
# `reachError` with the error reduced at every step

`reachError` never reduces in its own recursion, so it gains a box per step and
holds `k * n` generators: past `k = o` the subtrahend is described by more
generators than the run it comes off, which is bounded at `o * n` throughout.

A `reduce` per step caps it, and the *direction* is what makes that sound. The
error stands on the right of `reach_subset_reachSetExact_add_error`, added to the
exact set, so enlarging it keeps that inclusion — the reverse of the usual
situation, where enlarging a computed set is what breaks a guarantee. And
`reduce_outer` enlarges. So the price is precision, never soundness: the error
is bigger, and `reachInnerReduced` is correspondingly smaller.

What it buys is `reachErrorReduced_h_le` — `o * n` at every horizon, `k = 0`
included, which is the run's own bound.

Otherwise the recursion of `reachError` unchanged, and at the same instances:
`Zonotope` and `𝕋 = ℝ`, `mtimes` being exact only there.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `reach` owes after `k` steps, reduced at every step: the same
recursion as `reachError` with one `reduce` on top, which enlarges it and so
keeps it sound where it is used. -/
noncomputable def LinearSysDT.reachErrorReduced (sys : LinearSysDT ℝ n)
    (params : Reach.InputParams (Zonotope (Vec ℝ n)) (Zonotope (Vec ℝ n)) ℕ)
    (options : LinearSysDT.ReachOptions) :
    Zonotope (Vec ℝ n) :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let o := options.ρ
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let rec E : ℕ → Zonotope (Vec ℝ n)  -- E_k
    | 0 => Zonotope.ofPoint 0
    | k + 1 => Zonotope.reduce
        ((Zonotope.mtimes sys.A (E k)).plus
          (Zonotope.reduceBox
            ((Zonotope.mtimes sys.A (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ options)).plus U) o)) o
  E N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
