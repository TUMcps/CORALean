module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid

@[expose] public section

/-!
# A prefix of a valid signal is valid

The first `m ≥ 1` points of a valid signal, with their values, form a valid signal.

## Inputs
* `s` – signal
* `m` – number of kept points

## Hypotheses
* `hs` – the signal is valid
* `hm1` – at least one point is kept
* `hm2` – at most all points are kept

## Conclusion
* the prefix is a valid signal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A prefix of a valid signal is valid. -/
theorem PointSegmentSignal.isValid_take (s : PointSegmentSignal T) (hs : s.IsValid) (m : ℕ)
    (hm1 : 1 ≤ m) (hm2 : m ≤ s.timePoints.length) : -- --- CONCL ---
    (PointSegmentSignal.mk (s.timePoints.take m) (s.values.take (2 * m))).IsValid
      := by -- --- PROOF ---
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases List.take_eq_nil_iff.mp h with h | h
    · omega
    · exact h1 h
  · simp [List.length_take]; omega
  · obtain ⟨a, l, hl⟩ : ∃ a l, s.timePoints = a :: l := by
      cases h : s.timePoints with
      | nil => simp [h] at h1
      | cons a l => exact ⟨a, l, rfl⟩
    rw [hl] at h3 ⊢
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simpa using h3
  -- the times still increase
  · exact h4.sublist (List.take_sublist _ _)
  -- the points kept have the same neighbours as in `s`
  · intro i hi hi'
    simp only [List.length_take] at hi'
    have := h5 i hi (by omega)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD] at this ⊢
    simpa [List.getElem?_take, show 2 * i < 2 * m by omega, show 2 * i + 1 < 2 * m by omega,
      show 2 * i - 1 < 2 * m by omega] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
