module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Definitions.Refines
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


-- =============================  `FourValuedSignal.at_eq_ii_iff`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The signal is `Inconclusive` at a time exactly when `isInconclusive` holds there. -/
theorem FourValuedSignal.at_eq_ii_iff {T : Type} [LinearOrder T] (s : FourValuedSignal T) (t : T) :
    s.at t = FourValued.ii ↔ s.isInconclusive.at t = true := by
  unfold FourValuedSignal.at
  split_ifs with h <;> cases s.signal.at t <;> simp [h, FourValued.fromKleene]


-- ================================  `FourValuedSignal.eq_iff`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `eq` is structural equality of the two parts. -/
theorem FourValuedSignal.eq_iff {T : Type} [LinearOrder T] (a b : FourValuedSignal T) :
    a.eq b = true ↔ a = b := by
  obtain ⟨⟨a1, a2⟩, a3⟩ := a; obtain ⟨⟨b1, b2⟩, b3⟩ := b
  simp [FourValuedSignal.eq, KleeneSignal.eq, PointSegmentSignal.eq_iff]


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


-- ==============================  `FourValuedSignal.not_mapTime`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Negating keeps the time points, so the negation of a float signal read as reals is the negation
of the signal read as reals. -/
theorem FourValuedSignal.not_mapTime {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    (s : FourValuedSignal 𝕋) : s.not.mapTime Float.SoundFloatArithmetic.toReal =
      (s.mapTime Float.SoundFloatArithmetic.toReal).not := rfl


-- =============================  `FourValuedSignal.Refines.refl`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every signal refines itself. -/
theorem FourValuedSignal.Refines.refl (s : FourValuedSignal ℝ) : s.Refines s := fun _ _ _ => rfl


-- =============================  `FourValuedSignal.Refines.trans`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Refinement is transitive. -/
theorem FourValuedSignal.Refines.trans {a b c : FourValuedSignal ℝ} (h1 : a.Refines b)
    (h2 : b.Refines c) : a.Refines c := fun t ht hne => by
  rw [← h2 t ht hne]; exact h1 t ht (by rw [h2 t ht hne]; exact hne)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
