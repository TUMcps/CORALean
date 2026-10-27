module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachOrdersOptions

@[expose] public section

/-!
# `reach` with a per-step order

`reachOrders` re-chooses the order at every step, `o k` for `reach`'s one
fixed `o`; `reachOrders_const_eq_reach` recovers `reach` at a constant
sequence. Expressible, as [1]'s tuning algorithm needs, not *chosen*.

## Inputs
* `sys` – system
* `params` – reachability parameters with inputs
* `options` – reachability options with per-step orders

## Output
* the reachable set at the final time, with per-step orders

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reach` with the order re-chosen at every step: `ρ k` at step
`k`, in place of the one order `reach` fixes for the whole run. -/
def LinearSysDT.reachOrders (sys : LinearSysDT 𝕋 n) (params : Reach.InputParams (S n) (S n) ℕ)
    (options : LinearSysDT.ReachOrdersOptions) : S n :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let o := options.ρ
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let rec R : ℕ → S n                                              -- R_k, the run after k steps
    | 0 => R₀
    | k + 1 => reduce (plus (mtimes sys.A (R k)) U) (o (k + 1))    -- R_{k+1}
  R N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
