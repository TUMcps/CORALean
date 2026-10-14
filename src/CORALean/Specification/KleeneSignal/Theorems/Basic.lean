module

public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.NotAt
public import CORALean.Specification.PointSegmentSignal.Theorems.NotIsValid

@[expose] public section

/-!
# `KleeneSignal/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ==================================  `KleeneSignal.at_not`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The value of `~obj` at a time is the negation of the value of `obj`. -/
theorem KleeneSignal.at_not {T : Type} [LinearOrder T] [Zero T] (s : KleeneSignal T)
    (hs : s.IsValid) (t : T) : s.not.at t = (s.at t).not := by
  simp only [KleeneSignal.at, KleeneSignal.not, PointSegmentSignal.not_at _ hs.1]
  split_ifs <;> cases s.signal.at t <;> rfl


-- ==================================  `KleeneSignal.eq_iff`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `eq` is structural equality of the two parts. -/
theorem KleeneSignal.eq_iff {T : Type} [LinearOrder T] (a b : KleeneSignal T) :
    a.eq b = true ↔ a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp [KleeneSignal.eq]


-- ================================  `KleeneSignal.at_eq_of_eq`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Equal signals have the same value at every time. -/
theorem KleeneSignal.at_eq_of_eq {T : Type} [LinearOrder T] (a b : KleeneSignal T)
    (h : a.eq b = true) (t : T) : a.at t = b.at t := by
  rw [(KleeneSignal.eq_iff a b).mp h]


-- ================================  `KleeneSignal.not_isValid`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Negation keeps a signal valid. -/
theorem KleeneSignal.not_isValid {T : Type} [LinearOrder T] [Zero T] (s : KleeneSignal T)
    (hs : s.IsValid) : s.not.IsValid :=
  ⟨PointSegmentSignal.not_isValid _ hs.1, hs.2⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
