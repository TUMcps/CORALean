import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachOrdersOptions

/-!
# `reach` with a per-step order

`reachOrders` re-chooses the order at every step, `o k` for `reach`'s one
fixed `o`; `reachOrders_const_eq_reach` recovers `reach` at a constant
sequence. Expressible, as [1]'s tuning algorithm needs, not *chosen*.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reach` with the order re-chosen at every step: `zonotopeOrder k` at step
`k`, in place of the one order `reach` fixes for the whole run. -/
def LinearSysDT.reachOrders (sys : LinearSysDT 𝕋 n) (params : Reach.InputParams (S n) (S n) ℕ)
    (options : LinearSysDT.ReachOrdersOptions) : S n :=
  let R₀ := params.R0                                               -- the paper's symbols
  let U := params.U
  let o := options.zonotopeOrder
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let rec R : ℕ → S n                                              -- R_k, the run after k steps
    | 0 => R₀
    | k + 1 => reduce (plus (mtimes sys.A (R k)) U) (o (k + 1))    -- R_{k+1}
  R N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
