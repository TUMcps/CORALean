import CORALean.ContDynamics.LinearSysDT.Operations.Reach

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
-- Last update:   08-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reach` with the order re-chosen at every step: `o k` at step `k`, in place
of the one `o` `reach` fixes for the whole run. -/
def LinearSysDT.reachOrders (sys : LinearSysDT 𝕋 n) (o : ℕ → ℕ) (ho : ∀ k, 0 < o k)
    (R₀ U : S n) : ℕ → S n
  | 0 => R₀
  | k + 1 => reduce (plus (mtimes sys.A (sys.reachOrders o ho R₀ U k)) U) (o (k + 1))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
