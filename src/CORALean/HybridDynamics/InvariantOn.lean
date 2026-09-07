import CORALean.HybridDynamics.HybridAutomaton

/-!
# A set per location and jump count that a run cannot leave

`Invariant` indexed by the number of jumps taken so far, so a location visited
twice on the way to a bound need not be answered by the same set both times.
Flowing keeps the index; jumping raises it — the only difference from
`Invariant`, which is `RunOnOuter`'s two cases.

This generalises `Invariant` rather than replacing it:
`Theorems.InvariantOnOfInvariant` reads an unbounded invariant as the constant
family at every index. A bound on the horizon is then a statement about `k`,
`RunOn k` for `k ≤ K`, that a caller states for itself — nothing here builds an
inequality into the index.

Both fields are the same obligations `Invariant` states, discharged the same way
by `Theorems.FlowOuter` and `Theorems.JumpOuter`; only the bookkeeping of which
index a location's set is read at differs. `R` lives in the state's
representation `S` and the guard in `G`, as at `Invariant` (#39).
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure HybridAutomaton.InvariantOn (HA : HybridAutomaton S G L 𝕋 n) (R : ℕ → L → S n) :
    Prop where
  flow {k : ℕ} {ℓ : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} (h : (HA.loc ℓ).Trajectory τ x u)
    (h₀ : x 0 ∈ construct (R k ℓ)) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) :
    x t ∈ construct (R k ℓ)
  jump {k : ℕ} {ℓ : L} {e : Transition G L 𝕋 n} (hmem : e ∈ (HA.loc ℓ).trans)
    {z : Vec ℝ n} (hz : z ∈ construct (R k ℓ)) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (R (k + 1) e.target)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
