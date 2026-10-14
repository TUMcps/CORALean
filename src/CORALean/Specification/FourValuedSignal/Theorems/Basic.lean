module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Theorems.Basic

@[expose] public section

/-!
# `FourValuedSignal/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ================================  `FourValuedSignal.eq_iff`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `eq` is structural equality of the two parts. -/
theorem FourValuedSignal.eq_iff {T : Type} [LinearOrder T] (a b : FourValuedSignal T) :
    a.eq b = true ↔ a = b := by
  obtain ⟨⟨a1, a2⟩, a3⟩ := a; obtain ⟨⟨b1, b2⟩, b3⟩ := b
  simp [FourValuedSignal.eq, KleeneSignal.eq]


-- ==============================  `FourValuedSignal.at_eq_of_eq`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Equal signals have the same value at every time. -/
theorem FourValuedSignal.at_eq_of_eq {T : Type} [LinearOrder T] (a b : FourValuedSignal T)
    (h : a.eq b = true) (t : T) : a.at t = b.at t := by
  rw [(FourValuedSignal.eq_iff a b).mp h]


-- ==============================  `FourValuedSignal.not_isValid`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Negation keeps a signal valid. -/
theorem FourValuedSignal.not_isValid {T : Type} [LinearOrder T] [Zero T] (s : FourValuedSignal T)
    (hs : s.IsValid) : s.not.IsValid :=
  ⟨KleeneSignal.not_isValid _ hs.1, hs.2⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
