module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.HybridDynamics.Definitions.Transition

@[expose] public section

/-!
# Hybrid automata: a location

CORA's `location`: the invariant that holds while the run is here, the dynamics that govern it, and
the outgoing transitions, with the input and disturbance sets of CORA's `params.Uloc` and
`params.Wloc`. The dynamics are a `LinearSys` with its whole equation `ẋ = A x + B u + c + E w`;
the output equation plays no part in a stay. `inv` is in the guard's representation `G`, `U` and
`W` in the state's `S` (#39). `IsTrajectory` is one admissible stay on a local clock from `0` to
the dwell time `τ`, a Carathéodory run (`IsTrajectory.of_hasDerivWithinAt` admits a classical
stay); `Theorems.LinearEmbedding` hands it to `LinearSys`. `nonneg` is not bookkeeping: without it
`Set.Icc 0 τ` is empty and `x τ`, the state a jump reads, is unconstrained.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Location (S G : ℕ → Type) (L : Type) (𝕋 : Type) (n : ℕ) where
  inv : G n
  dynamics : LinearSys 𝕋 n
  U : S dynamics.m
  W : S dynamics.r
  trans : List (Transition G L 𝕋 n)

/-- A stay of length `τ`: the state under inputs in `U` and disturbances in `W`, by the whole
state equation, inside the invariant throughout. -/
structure Location.IsTrajectory (ℓ : Location S G L 𝕋 n) (τ : ℝ) (x : ℝ → Vec ℝ n)
    (u : ℝ → Vec ℝ ℓ.dynamics.m) (w : ℝ → Vec ℝ ℓ.dynamics.r) : Prop where
  nonneg : 0 ≤ τ
  input (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : u t ∈ construct ℓ.U
  dist (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : w t ∈ construct ℓ.W
  meas : AEStronglyMeasurable (fun s => toRealMat ℓ.dynamics.A *ᵥ x s +
    toRealMat ℓ.dynamics.B *ᵥ u s + toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w s)
      (volume.restrict (Set.Icc 0 τ))
  integrable (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : IntervalIntegrable (fun s =>
    toRealMat ℓ.dynamics.A *ᵥ x s + toRealMat ℓ.dynamics.B *ᵥ u s + toRealVec ℓ.dynamics.c +
      toRealMat ℓ.dynamics.E *ᵥ w s) volume 0 t
  cont : ContinuousOn x (Set.Icc 0 τ)
  flow (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : x t = x 0 + ∫ s in (0:ℝ)..t,
    (toRealMat ℓ.dynamics.A *ᵥ x s + toRealMat ℓ.dynamics.B *ᵥ u s + toRealVec ℓ.dynamics.c +
      toRealMat ℓ.dynamics.E *ᵥ w s)
  invariant (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : x t ∈ construct ℓ.inv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
