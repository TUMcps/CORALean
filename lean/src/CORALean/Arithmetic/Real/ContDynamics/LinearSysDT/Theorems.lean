import CORALean.Arithmetic.Real.ContDynamics.LinearSysDT.Proofs.API

/-!
# What `LinearSysDT` guarantees

One entry per operation in `API`, stated in full and discharged by the lemma of
the same name in `LinearSysDT.Proofs`.
-/

namespace CORALean.Arithmetic.Real

open ContSet Scalar OuterContSet

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n] [OuterContSet S 𝕋]

theorem LinearSysDT.reach_outer (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ U k) :=
  LinearSysDT.Proofs.reach_outer sys o R₀ U traj k

end CORALean.Arithmetic.Real
