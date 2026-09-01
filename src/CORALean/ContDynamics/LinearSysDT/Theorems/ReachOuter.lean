import CORALean.ContDynamics.LinearSysDT.Operations

/-!
# `LinearSysDT.reach` contains every trajectory

Induction on the step count, applying the two guarantees in the order `reach`
applies the operations. The only facts used about `construct` are `plus_outer`,
`reduce_outer` and `mtimes_outer`, so a representation buys into this by proving
those three and nothing else.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]

theorem LinearSysDT.reach_outer (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ U k) := by
  induction k with
  | zero => exact traj.init
  | succ k ih =>
    show x (k + 1) ∈ construct (reduce (plus (mtimes sys.A (sys.reach o R₀ U k)) U) o)
    rw [traj.step k]
    exact reduce_outer _ _ (plus_outer _ _
      (Set.add_mem_add
        (mtimes_outer sys.A _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ ih)))
        (traj.input k)))

end CORALean.Real
