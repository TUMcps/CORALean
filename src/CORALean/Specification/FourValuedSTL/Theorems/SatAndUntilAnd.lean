module

public import CORALean.Specification.FourValuedSTL.FourValuedSTL
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet
public import CORALean.Specification.STLInterval.Operations.Basic
public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# The until that holds the left formula at both ends

The strict until of [1, Sec. 2.5] does not require `φ₁` at `t` or `t'`; the until of [26, 35],
which does, is recovered as `φ₁ ∧ φ₁ U_I (φ₁ ∧ φ₂)`: it holds at `t` iff there is `t' ∈ t ⊕ I` with
`φ₂` at `t'` and `φ₁` at every time of the closed interval `[t, t']`.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSTL.Formula.sat_and_until_and {X : Type} (φ₁ φ₂ : FourValuedSTL.Formula X)
    (I : STLInterval) (ξ : ℝ≥0 → X) (t : ℝ≥0) :
    (FourValuedSTL.Formula.and φ₁ (.until I φ₁ (.and φ₁ φ₂))).Sat ξ t ↔
      ∃ t' : ℝ≥0, (t' : ℝ) - t ∈ I.set ∧ φ₂.Sat ξ t' ∧
        ∀ t'' : ℝ≥0, t ≤ t'' → t'' ≤ t' → φ₁.Sat ξ t'' := by -- --- PROOF ---
  simp only [FourValuedSTL.Formula.Sat]
  constructor
  · -- `φ₁` at `t`, at `t'`, and strictly between
    rintro ⟨h0, t', hu, ⟨h1, h2⟩, hl⟩
    refine ⟨t', hu, h2, fun t'' ht1 ht2 => ?_⟩
    rcases ht1.eq_or_lt with rfl | hlt
    · exact h0
    · rcases ht2.eq_or_lt with rfl | hlt'
      · exact h1
      · exact hl t'' hlt hlt'
  · rintro ⟨t', hu, h2, hl⟩
    have hd := STLInterval.zero_le_of_mem_set I _ hu
    have htt : t ≤ t' := by exact_mod_cast (by linarith : (t : ℝ) ≤ t')
    exact ⟨hl t le_rfl htt, t', hu, ⟨hl t' htt le_rfl, h2⟩, fun t'' h1 h2 => hl t'' h1.le h2.le⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
