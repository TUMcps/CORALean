module

public import CORALean.Specification.KleeneSignal.Theorems.IsRefinedByIff
public import CORALean.Specification.PointSegmentSignal.Theorems.UntilMono

@[expose] public section

/-!
# The until of the under- and overapproximations bounds the until of every refinement

For valid three-valued signals `Λ₁`, `Λ₂` and valid Boolean refinements `λ₁ ≺ Λ₁`, `λ₂ ≺ Λ₂`,
at every time `t ≥ 0`: `⌊Λ₁⌋ U_I ⌊Λ₂⌋ ⊑ₜ λ₁ U_I λ₂ ⊑ₜ ⌈Λ₁⌉ U_I ⌈Λ₂⌉`, so the first underapproximates
and the second overapproximates every `λ₁ U_I λ₂` ([1, Sec. 4.2 (monotonicity)]).

## Inputs
* `s₁` – left three-valued signal
* `s₂` – right three-valued signal
* `l₁` – left Boolean refinement
* `l₂` – right Boolean refinement
* `U` – time interval

## Hypotheses
* `h₁` – the left signal is valid
* `h₂` – the right signal is valid
* `hl₁` – the left refinement is valid
* `hl₂` – the right refinement is valid
* `hr₁` – the left refinement refines the left signal
* `hr₂` – the right refinement refines the right signal

## Conclusion
* the refinements' until lies between the under- and overapproximation untils

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.until_between_refinements (s₁ s₂ : KleeneSignal ℝ) (h₁ : s₁.IsValid)
    (h₂ : s₂.IsValid) (l₁ l₂ : PointSegmentSignal ℝ) (hl₁ : l₁.IsValid) (hl₂ : l₂.IsValid)
    (hr₁ : s₁.IsRefinedBy l₁) (hr₂ : s₂.IsRefinedBy l₂) (U : STLInterval ℝ) : -- --- CONCL ---
    ∀ t : ℝ, 0 ≤ t →
      ((s₁.toBoolSignal false).until U (s₂.toBoolSignal false)).at t ≤ (l₁.until U l₂).at t ∧
      (l₁.until U l₂).at t ≤
        ((s₁.toBoolSignal true).until U (s₂.toBoolSignal true)).at t := by -- --- PROOF ---
  rw [KleeneSignal.isRefinedBy_iff s₁ h₁] at hr₁
  rw [KleeneSignal.isRefinedBy_iff s₂ h₂] at hr₂
  have f₁ := (KleeneSignal.toBoolSignal_spec s₁ h₁ false).1
  have f₂ := (KleeneSignal.toBoolSignal_spec s₂ h₂ false).1
  have c₁ := (KleeneSignal.toBoolSignal_spec s₁ h₁ true).1
  have c₂ := (KleeneSignal.toBoolSignal_spec s₂ h₂ true).1
  intro t ht
  exact ⟨PointSegmentSignal.until_mono _ _ _ _ f₁ hl₁ f₂ hl₂ U (fun x hx => (hr₁ x hx).1)
      (fun x hx => (hr₂ x hx).1) t ht,
    PointSegmentSignal.until_mono _ _ _ _ hl₁ c₁ hl₂ c₂ U (fun x hx => (hr₁ x hx).2)
      (fun x hx => (hr₂ x hx).2) t ht⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
