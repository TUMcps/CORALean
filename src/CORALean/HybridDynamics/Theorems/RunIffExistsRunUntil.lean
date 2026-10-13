module

public import CORALean.HybridDynamics.Theorems.RunOnToRun
public import CORALean.HybridDynamics.Theorems.RunUntilToRunOn

@[expose] public section

/-!
# A run is a run of bounded duration

`Run` carries no clock, and `RunUntil` adds nothing but one: every run lasts
some finite time `T` — the sum of its dwell times — and takes some number `k`
of jumps, and is then a `RunUntil T k`; conversely `RunUntil.toRunOn` forgets
both. So `RunUntil T k` is exactly a `Run` together with a duration of at most
`T` and `k` jumps, and a guarantee stated over it, `reachFloat_outer`, speaks of
the runs the automaton defines.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A budget some run fits is not negative, its first stay being no longer. -/
theorem aux_runUntil_nonneg {HA : HybridAutomaton S G L 𝕋 n} {T : ℝ} {k : ℕ} {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.RunUntil T k ℓ x ℓ' y) : 0 ≤ T := by
  cases run with
  | flow h hτ => exact h.nonneg.trans hτ
  | jump h hτ => exact h.nonneg.trans hτ


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.run_iff_exists_runUntil {HA : HybridAutomaton S G L 𝕋 n} {ℓ ℓ' : L}
    {x y : Vec ℝ n} :
    HA.Run ℓ x ℓ' y ↔ ∃ (T : ℝ) (k : ℕ), HA.RunUntil T k ℓ x ℓ' y := by -- --- PROOF ---
  constructor
  · intro run
    induction run with
    | @flow _ τ _ _ h => exact ⟨τ, 0, .flow h le_rfl⟩
    | @jump _ _ τ _ _ _ _ h hmem hguard _ ih =>
      -- the stay's dwell time added to the rest's duration
      obtain ⟨T, k, rest⟩ := ih
      refine ⟨τ + T, k + 1, .jump h (by linarith [aux_runUntil_nonneg rest]) hmem hguard ?_⟩
      rwa [add_sub_cancel_left]
  · rintro ⟨T, k, run⟩
    exact run.toRunOn.toRun

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
