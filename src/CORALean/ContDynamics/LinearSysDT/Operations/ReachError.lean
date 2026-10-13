module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

@[expose] public section

/-!
# What a run of `reach` owes

`plus` and `mtimes` are exact at `Zonotope`, so a step loses ground only where
it reduces, and `reduceBox` names that step's error exactly. What the run owes
after `k + 1` steps is therefore this step's box together with everything owed
after `k`, carried forward by one application of `A`: a box dropped at step `j`
reaches step `k` multiplied by `A` exactly `k - 1 - j` times, which the
recursion produces without ever writing that power down.

At `Zonotope` and at `𝕋 = ℝ`, not at the `Reduce` class. The class obliges the
outer direction only, so no box for the reverse one can be read off it; and
`Mtimes (Mat ℝ) 𝒵` is the matrix instance whose `mtimes` is exact, which is
what carrying an error forward needs.

A zonotope rather than a `Set`: nonemptiness and boundedness then come from the
representation, and `minkDiffRep` can take it as an operand.
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

/-- What `reach` owes after `k` steps: every step's reduction box, each carried
forward by one `A` per step taken since. -/
noncomputable def LinearSysDT.reachError (sys : LinearSysDT ℝ n)
    (params : Reach.InputParams (Zonotope (Vec ℝ n)) (Zonotope (Vec ℝ n)) ℕ)
    (options : LinearSysDT.ReachOptions) :
    Zonotope (Vec ℝ n) :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let o := options.ρ
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let rec E : ℕ → Zonotope (Vec ℝ n)  -- E_k
    | 0 => Zonotope.ofPoint 0
    | k + 1 => (Zonotope.mtimes sys.A (E k)).plus
        (Zonotope.reduceBox
          ((Zonotope.mtimes sys.A (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ options)).plus U) o)
  E N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
