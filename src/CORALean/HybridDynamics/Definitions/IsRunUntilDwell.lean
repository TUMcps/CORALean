module

public import CORALean.HybridDynamics.Definitions.IsRunUntil

@[expose] public section

/-!
# A run of bounded duration, optionally with positive dwell time at every jump

`IsRunUntil` with a switch `dw`: with `dw = false` the runs are those of `IsRunUntil`, with
`dw = true` every stay before a jump lasts `τ > 0`. A run that jumps at once, from a state on the
guard it starts at, is not a run to a reachability algorithm that drops the sets whose flow points
strictly into the invariant at the guard (CORA's `checkFlow`); those sets are where such a run
would go.

## Inputs
* `HA` – hybrid automaton
* `dw` – whether every jump has positive dwell time
* `T` – time budget
* `k` – number of jumps
* `ℓ` – start location
* `x` – start state
* `ℓ'` – end location
* `y` – end state

## Output
* the statement that there is a run of at most `T` with exactly `k` jumps, with positive dwell
  times if `dw`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSetLike Scalar


-- ========================================  MAIN TYPE  ========================================= --

/-- A run with exactly `k` jumps, lasting at most `T` in all, every stay before a jump positive if
`dw`. -/
inductive HybridAutomaton.IsRunUntilDwell {S G : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
    [∀ n, ContSetLike (G n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
    (HA : HybridAutomaton S G L 𝕋 n) (dw : Bool) :
    ℝ → ℕ → L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {T : ℝ} {ℓ : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} (h : (HA.loc ℓ).IsTrajectory τ x u w)
      (hτ : τ ≤ T) : HA.IsRunUntilDwell dw T 0 ℓ (x 0) ℓ (x τ)
  | jump {T : ℝ} {k : ℕ} {ℓ ℓ' : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} {y : Vec ℝ n}
      {e : Transition G L 𝕋 n} (h : (HA.loc ℓ).IsTrajectory τ x u w) (hτ : τ ≤ T)
      (hdw : dw = true → 0 < τ) (hmem : e ∈ (HA.loc ℓ).trans) (hguard : x τ ∈ toSet e.guard)
      (rest : HA.IsRunUntilDwell dw (T - τ) k e.target (e.reset (x τ)) ℓ' y) :
      HA.IsRunUntilDwell dw T (k + 1) ℓ (x 0) ℓ' y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
