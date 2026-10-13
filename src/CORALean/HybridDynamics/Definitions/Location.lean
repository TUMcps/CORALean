import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.HybridDynamics.Definitions.Transition

/-!
# Hybrid automata: a location

CORA's `location`: the invariant that holds while the run is here, the dynamics
that govern it, the input set those dynamics draw from, and the outgoing
transitions.

`inv` is in the guard's representation `G` and `U` in the state's `S`: the
invariant is only ever read through `construct`, where `U` is propagated, so
this file asks `ContSet` of `G` and nothing more (#39). `LinearSys` dynamics,
because that is what the reachability machinery encloses today.

`Trajectory` is what a location denotes — one admissible stay, on a *local*
clock from `0` to the dwell time `τ`, so global time never appears and every
`LinearSys` statement is used unchanged. The initial state is the point `x 0`;
`Theorems.LinearEmbedding` converts by naming a set it lies in.

`nonneg` is not bookkeeping: without it `Set.Icc 0 τ` is empty, every field
holds vacuously, and `x τ` — the state a jump reads — is unconstrained.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Location (S G : ℕ → Type) (L : Type) (𝕋 : Type) (n : ℕ) where
  inv : G n
  dynamics : LinearSys 𝕋 n
  U : S n
  trans : List (Transition G L 𝕋 n)

structure Location.Trajectory (ℓ : Location S G L 𝕋 n) (τ : ℝ)
    (x u : ℝ → Vec ℝ n) : Prop where
  nonneg : 0 ≤ τ
  input (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : u t ∈ construct ℓ.U
  flow (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    HasDerivWithinAt x (toRealMat ℓ.dynamics.A *ᵥ x t + u t) (Set.Icc 0 τ) t
  invariant (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : x t ∈ construct ℓ.inv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
