module

public import CORALean.Specification.FourValuedSTL.Definitions.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.UntilSpec
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet
public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# The satisfaction signal of an until is the until of the satisfaction signals

If the Boolean signals `λ₁`, `λ₂` (valid, i.e. of finite variability) are the satisfaction signals
of `φ₁`, `φ₂` over `ξ`, then `λ₁ U_I λ₂`, the until of Boolean signals, is the satisfaction signal
of `φ₁ U_I φ₂`: `⟦φ₁ U_I φ₂⟧_ξ = ⟦φ₁⟧_ξ U_I ⟦φ₂⟧_ξ` ([1, Lemma 2 (STL)], the second statement
of [1, Lemma 2]). It is `PointSegmentSignal.until_spec` read against the Boolean semantics of
[1, Sec. 2.5].

## Inputs
* `X` – state type
* `φ₁` – left formula
* `φ₂` – right formula
* `I` – time interval
* `ξ` – execution
* `l₁` – Boolean signal of the left formula
* `l₂` – Boolean signal of the right formula

## Hypotheses
* `hl₁` – the left signal is valid
* `hl₂` – the right signal is valid
* `h₁` – the left signal is the left formula's satisfaction
* `h₂` – the right signal is the right formula's satisfaction

## Conclusion
* the until of the signals is valid and is the until formula's satisfaction

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `⟦φ⟧_ξ(t) = ⊤` iff `φ` holds of `ξ` at `t`, [1, Sec. 2.5]. -/
private theorem FourValuedSTL.Formula.aux_satBool_eq_true_iff {X : Type}
    (φ : FourValuedSTL.Formula X)
    (ξ : ℝ≥0 → X) (t : ℝ≥0) : φ.satBool ξ t = true ↔ φ.Satisfies ξ t := by
  simp [FourValuedSTL.Formula.satBool]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSTL.Formula.satBool_until {X : Type} (φ₁ φ₂ : FourValuedSTL.Formula X)
    (I : STLInterval ℝ) (ξ : ℝ≥0 → X)
    (l₁ l₂ : PointSegmentSignal ℝ) (hl₁ : l₁.IsValid) (hl₂ : l₂.IsValid)
    (h₁ : ∀ t : ℝ≥0, l₁.at t = φ₁.satBool ξ t)
    (h₂ : ∀ t : ℝ≥0, l₂.at t = φ₂.satBool ξ t) : -- --- CONCL ---
    (l₁.until I l₂).IsValid ∧ ∀ t : ℝ≥0,
      (l₁.until I l₂).at t =
        (FourValuedSTL.Formula.until I φ₁ φ₂).satBool ξ t := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := PointSegmentSignal.until_spec l₁ l₂ hl₁ hl₂ I
  refine ⟨hv, fun t => ?_⟩
  -- the two Boolean values are equal iff the two conditions are equivalent
  have e₁ := fun t' => (iff_of_eq (congrArg (· = true) (h₁ t'))).trans
    (FourValuedSTL.Formula.aux_satBool_eq_true_iff φ₁ ξ t')
  have e₂ := fun t' => (iff_of_eq (congrArg (· = true) (h₂ t'))).trans
    (FourValuedSTL.Formula.aux_satBool_eq_true_iff φ₂ ξ t')
  have key : (l₁.until I l₂).at t = true ↔ (FourValuedSTL.Formula.until I φ₁ φ₂).Satisfies ξ t := by
    rw [h t t.2]
    simp only [FourValuedSTL.Formula.Satisfies]
    constructor
    · rintro ⟨t', hu, hr, hl⟩
      have hd := STLInterval.zero_le_of_mem_set I _ hu
      have ht' : 0 ≤ t' := by have := NNReal.coe_nonneg t; linarith
      refine ⟨⟨t', ht'⟩, hu, (e₂ ⟨t', ht'⟩).1 hr, fun t'' h1 h2 => ?_⟩
      exact (e₁ t'').1 (hl t'' (by exact_mod_cast h1) (by exact_mod_cast h2))
    · rintro ⟨t', hu, hr, hl⟩
      refine ⟨t', hu, (e₂ t').2 hr, fun x hx1 hx2 => ?_⟩
      have hx0 : 0 ≤ x := by have := NNReal.coe_nonneg t; linarith
      exact (e₁ ⟨x, hx0⟩).2 (hl ⟨x, hx0⟩ (by exact_mod_cast hx1) (by exact_mod_cast hx2))
  exact Bool.eq_iff_iff.2 (key.trans (FourValuedSTL.Formula.aux_satBool_eq_true_iff _ ξ t).symm)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
