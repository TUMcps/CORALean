module

public import CORALean.HybridDynamics.Theorems.IsRunOnToIsRun
public import CORALean.HybridDynamics.Theorems.IsRunUntilToIsRunOn

@[expose] public section

/-!
# A run is a run of bounded duration

`IsRun` carries no clock, and `IsRunUntil` adds nothing but one: every run lasts
some finite time `T` — the sum of its dwell times — and takes some number `k`
of jumps, and is then a `IsRunUntil T k`; conversely `IsRunUntil.toIsRunOn` forgets
both. So `IsRunUntil T k` is exactly a `IsRun` together with a duration of at most
`T` and `k` jumps, and a guarantee stated over it, `reachFloat_outer`, speaks of
the runs the automaton defines.

## Inputs
* `HA` – hybrid automaton
* `ℓ` – location
* `ℓ'` – end location
* `x` – trajectory of the stay
* `y` – end state

## Hypotheses
* none

## Conclusion
* a run is a run of some bounded duration and jump count
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A budget some run fits is not negative, its first stay being no longer. -/
theorem aux_runUntil_nonneg {HA : HybridAutomaton S G L 𝕋 n} {T : ℝ} {k : ℕ} {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.IsRunUntil T k ℓ x ℓ' y) : 0 ≤ T := by
  cases run with
  | flow h hτ => exact h.nonneg.trans hτ
  | jump h hτ => exact h.nonneg.trans hτ


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.isRun_iff_exists_isRunUntil {HA : HybridAutomaton S G L 𝕋 n} {ℓ ℓ' : L}
    {x y : Vec ℝ n} : -- --- CONCL ---
    HA.IsRun ℓ x ℓ' y ↔ ∃ (T : ℝ) (k : ℕ), HA.IsRunUntil T k ℓ x ℓ' y := by -- --- PROOF ---
  constructor
  · intro run
    induction run with
    | @flow _ τ _ _ _ h => exact ⟨τ, 0, .flow h le_rfl⟩
    | @jump _ _ τ _ _ _ _ _ h hmem hguard _ ih =>
      -- the stay's dwell time added to the rest's duration
      obtain ⟨T, k, rest⟩ := ih
      refine ⟨τ + T, k + 1, .jump h (by linarith [aux_runUntil_nonneg rest]) hmem hguard ?_⟩
      rwa [add_sub_cancel_left]
  · rintro ⟨T, k, run⟩
    exact run.toIsRunOn.toIsRun

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
