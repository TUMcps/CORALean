import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.HybridDynamics.Transition

/-!
# Hybrid automata: a location

CORA's `location`: the invariant that holds while the run is here, the dynamics
that govern it, the input set those dynamics draw from, and the outgoing
transitions.

`LinearSys` dynamics, because that is what the reachability machinery encloses
today. A nonlinear location is the same structure at `NonlinearSys`.

`Trajectory` is what a location denotes — one admissible stay, on a *local* clock
running from `0` to the dwell time `τ`, so a run's global time is the sum of the
dwell times and never appears. That is what lets every reachability statement in
`LinearSys` be used unchanged, all of them reading `Set.Icc 0 r ⊆ T`. The initial
state is the point `x 0` rather than a set; `Theorems.LinearEmbedding` converts by
naming a set the point lies in.

`nonneg` is not bookkeeping: without it `Set.Icc 0 τ` is empty, every field holds
vacuously, and `x τ` — the state a jump reads — is unconstrained.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}

structure Location (S : ℕ → Type) (L : Type) (𝕋 : Type) (n : ℕ) where
  inv : S n
  dynamics : LinearSys 𝕋 n
  U : S n
  trans : List (Transition S L 𝕋 n)

structure Location.Trajectory (ℓ : Location S L 𝕋 n) (τ : ℝ)
    (x u : ℝ → Vec ℝ n) : Prop where
  nonneg : 0 ≤ τ
  input (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : u t ∈ construct ℓ.U
  flow (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    HasDerivWithinAt x (toRealMat ℓ.dynamics.A *ᵥ x t + u t) (Set.Icc 0 τ) t
  invariant (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : x t ∈ construct ℓ.inv

/-- The state a jump reads, packaged as the membership the endpoint always has. -/
theorem Location.Trajectory.mem_Icc_right {ℓ : Location S L 𝕋 n} {τ : ℝ}
    {x u : ℝ → Vec ℝ n} (traj : ℓ.Trajectory τ x u) : τ ∈ Set.Icc 0 τ :=
  ⟨traj.nonneg, le_refl τ⟩

end CORALean.Real
