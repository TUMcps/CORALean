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
# `reachErrorOrders` with the error reduced at every step

`reachErrorReduced` at a per-step order sequence: the same recursion, one
`reduce` on top read at `o (k + 1)` in place of the one fixed `o`. The
direction is what keeps it sound at any sequence, exactly as for the fixed
order — the error stands on the right of `reach_subset_reachSet_add_error`, so
enlarging it keeps that inclusion regardless of which order enlarged it.

Otherwise the recursion of `reachErrorOrders` unchanged, and at the same
instances: `Zonotope` and `𝕋 = ℝ`.
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

/-- What `reachOrders` owes after `k` steps, reduced at every step: the same
recursion as `reachErrorOrders` with one `reduce` on top, at that step's own
order. -/
noncomputable def LinearSysDT.reachErrorReducedOrders (sys : LinearSysDT ℝ n)
    (params : Reach.InputParams (Zonotope (Vec ℝ n)) (Zonotope (Vec ℝ n)) ℕ)
    (options : LinearSysDT.ReachOrdersOptions) :
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
            ((Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) ⟨R₀, U, 0, k⟩ options)).plus U)
            (o (k + 1))))
        (o (k + 1))
  E N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
