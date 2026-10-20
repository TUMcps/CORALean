module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# `LinearSysDT.reach`, packaged as `Reach`'s `SetUnion`

The steps `0` through `K = tFinal - tStart` of `reach`, one per branch of the
`SetUnion` — the `Reach.reach` field of the instance. Computable wherever `reach`
is: no `reduce`, no new arithmetic, `List.map` over its steps.

## Inputs
* `sys` – system
* `params` – reachability parameters with inputs
* `options` – reachability options

## Output
* the reachable sets of all steps, as a union
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The steps `0` through `tFinal - tStart` of `reach`, from `R0` under inputs in
`U`, one `SetUnion` branch each. -/
def LinearSysDT.reachUnion (sys : LinearSysDT 𝕋 n) (params : Reach.InputParams (S n) (S n) ℕ)
    (options : LinearSysDT.ReachOptions) : SetUnion (S n) :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let K := params.tFinal - params.tStart                           -- steps
  ⟨(List.range (K + 1)).map (fun k => sys.reach ⟨R₀, U, 0, k⟩ options)⟩  -- ⋃_{k ≤ K} R(k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
