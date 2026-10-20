module

public import CORALean.Specification.PointSegmentSignal.Theorems.NotAt
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The negation of Boolean signals is antitone

If `λ ⊑ₜ λ'` at every time `t ≥ 0`, then `¬λ' ⊑ₜ ¬λ` there ([1, Sec. 4.2 (monotonicity)]).

## Inputs
* `l` – Boolean signal
* `l'` – larger signal

## Hypotheses
* `hl` – the signal is valid
* `hl'` – the larger signal is valid
* `h` – the signal is below the larger one at all times

## Conclusion
* the negations are in reverse order at all times

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.not_anti (l l' : PointSegmentSignal ℝ) (hl : l.IsValid)
    (hl' : l'.IsValid) (h : ∀ t : ℝ, 0 ≤ t → l.at t ≤ l'.at t) : -- --- CONCL ---
    ∀ t : ℝ, 0 ≤ t → l'.not.at t ≤ l.not.at t := by -- --- PROOF ---
  intro t ht
  rw [PointSegmentSignal.not_at l hl, PointSegmentSignal.not_at l' hl']
  have := h t ht
  revert this
  cases l.at t <;> cases l'.at t <;> simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
