import CORALean.Arithmetic.Real.ContDynamics.LinearSysDT.API

/-!
# `LinearSysDT.reach` contains every trajectory

Induction on the step count, applying the two guarantees in the order `reach`
applies the operations.

No representation can be named here: the only facts about `construct` are the
two `OuterContSet` fields. A representation buys into the theorem by proving
them.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real.LinearSysDT.Proofs

open Matrix Pointwise ContSet Scalar OuterContSet

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n] [OuterContSet S 𝕋]

theorem reach_outer (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ U k) := by
  induction k with
  | zero => exact traj.init
  | succ k ih =>
    show x (k + 1) ∈ construct (reduce o (plus (mtimes sys.A (sys.reach o R₀ U k)) U))
    rw [traj.step k]
    exact reduce_outer _ _ (plus_outer _ _
      (Set.add_mem_add (mtimes_outer sys.A _ (Set.mem_image_of_mem _ ih)) (traj.input k)))

end CORALean.Arithmetic.Real.LinearSysDT.Proofs
