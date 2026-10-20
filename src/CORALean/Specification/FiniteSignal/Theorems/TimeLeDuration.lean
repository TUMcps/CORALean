module

public import CORALean.Specification.FiniteSignal.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.Operations.Basic

@[expose] public section

/-!
# The duration is the last time

For a valid signal the duration is one of the times and no time exceeds it.

## Inputs
* `T` – time type
* `V` – value type
* `s` – signal

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* the duration is a time and no time exceeds it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.time_le_duration {T V : Type} [LinearOrder T] [Zero T] (s : FiniteSignal T V)
    (hs : s.IsValid) : s.duration ∈ s.time ∧ ∀ x ∈ s.time, x ≤ s.duration := by -- --- PROOF ---
  obtain ⟨hne, -, hp, -, -⟩ := hs
  rcases List.eq_nil_or_concat s.time with h | ⟨init, last, h⟩
  · exact absurd h hne
  · have hd : s.duration = last := by simp [FiniteSignal.duration, h]
    rw [h, List.concat_eq_append, List.pairwise_append] at hp
    rw [hd, h, List.concat_eq_append]
    refine ⟨by simp, fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact (hp.2.2 x hx last (by simp)).le
    · simp at hx; exact hx.le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
