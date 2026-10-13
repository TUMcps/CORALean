module

public import CORALean.HybridDynamics.HybridAutomaton

@[expose] public section

/-!
# A run of bounded duration

`RunOn` with a time budget: a run with exactly `k` jumps whose stays together
last at most `T`. Each stay of length `τ` spends `τ` of it and the rest of the
run is left `T - τ`, so `T` is a bound on *global* time, as CORA's `tFinal` is,
though no `Run` here carries a clock: the budget is what stands in for one.

A reachability algorithm run to a finite horizon answers for exactly these,
`HybridAutomaton.reachFloat_outer` among them; `Theorems.RunUntilToRunOn`
forgets the budget, so every such run is one of `RunOn`'s and of `Run`'s.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar


-- ========================================  MAIN TYPE  ========================================= --

/-- A run with exactly `k` jumps, from `x` at `ℓ` to `y` at `ℓ'`, lasting at most `T` in all. -/
inductive HybridAutomaton.RunUntil {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
    (HA : HybridAutomaton S G L 𝕋 n) :
    ℝ → ℕ → L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {T : ℝ} {ℓ : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} (h : (HA.loc ℓ).Trajectory τ x u)
      (hτ : τ ≤ T) : HA.RunUntil T 0 ℓ (x 0) ℓ (x τ)
  | jump {T : ℝ} {k : ℕ} {ℓ ℓ' : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} {y : Vec ℝ n}
      {e : Transition G L 𝕋 n} (h : (HA.loc ℓ).Trajectory τ x u) (hτ : τ ≤ T)
      (hmem : e ∈ (HA.loc ℓ).trans) (hguard : x τ ∈ construct e.guard)
      (rest : HA.RunUntil (T - τ) k e.target (e.reset (x τ)) ℓ' y) :
      HA.RunUntil T (k + 1) ℓ (x 0) ℓ' y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
