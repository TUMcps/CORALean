module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

@[expose] public section

/-!
# What a run of `reachOrders` owes

`reachError` at a per-step order sequence: the same recursion, `reduceBox`
read at `o (k + 1)` — the order the sequence supplies for the step just
taken — in place of the one fixed `o` `reachError` reduces to throughout.

At `Zonotope` and at `𝕋 = ℝ`, for the reasons `reachError`'s own docstring
gives: `mtimes` is exact only there, and a zonotope rather than a `Set` is what
`minkDiffRep` can take as an operand.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `reachOrders` owes after `k` steps: every step's reduction box, read
at that step's own order, each carried forward by one `A` per step taken
since. -/
noncomputable def LinearSysDT.reachErrorOrders (sys : LinearSysDT ℝ n)
    (params : Reach.InputParams (Zonotope (Vec ℝ n)) (Zonotope (Vec ℝ n)) ℕ)
    (options : LinearSysDT.ReachOrdersOptions) :
    Zonotope (Vec ℝ n) :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let o := options.ρ
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let rec E : ℕ → Zonotope (Vec ℝ n)  -- E_k
    | 0 => Zonotope.ofPoint 0
    | k + 1 => (Zonotope.mtimes sys.A (E k)).plus
        (Zonotope.reduceBox
          ((Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) ⟨R₀, U, 0, k⟩ options)).plus U)
          (o (k + 1)))
  E N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
