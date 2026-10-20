module

public import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.ConZonotope.Float.Operations.Plus
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.MemSlabNominalIff

@[expose] public section

/-!
# `ConZonotope.plus` over-approximates the Minkowski sum

The zonotope's argument with one step added, and that step costs nothing: the
concatenated coefficients satisfy the padded constraints exactly when each half
satisfies its own, which is `mem_stackRows_nominal_iff` composed with `blockLeft_append`. Only
the center rounds, and its residual is what the box absorbs.

## Inputs
* `cZ₁` – first summand
* `cZ₂` – second summand

## Hypotheses
* none

## Conclusion
* the Minkowski sum is contained in the result
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the projection
because that is the form the goal has. -/
theorem ConZonotope.aux_sum_univ_plus {cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)}
    (f : Fin (cZ₁.h + cZ₂.h) → ℝ) :
    ∑ j : Fin (cZ₁.plus cZ₂).h, f j
      = ∑ j, f (Fin.castAdd cZ₂.h j) + ∑ j, f (Fin.natAdd cZ₁.h j) :=
  Fin.sum_univ_add f

theorem ConZonotope.aux_plus_nominal (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    nominalSet cZ₁ + nominalSet cZ₂ ⊆
      nominalSet (cZ₁.plus cZ₂)
        + (Zonotope.centerResidual cZ₁.c cZ₂.c).construct := by -- --- PROOF ---
  rintro _ ⟨z₁, hz₁', z₂, hz₂', rfl⟩
  obtain ⟨β₁, hβ₁, hP₁, hz₁⟩ := ConZonotope.mem_nominalSet_iff.mp hz₁'
  obtain ⟨β₂, hβ₂, hP₂, hz₂⟩ := ConZonotope.mem_nominalSet_iff.mp hz₂'
  refine ⟨fun i => toReal ((cZ₁.plus cZ₂).c i)
            + ∑ j, toReal ((cZ₁.plus cZ₂).G j i) * Fin.append β₁ β₂ j,
          ConZonotope.mem_nominalSet_iff.mpr ⟨Fin.append β₁ β₂, ?_, ?_, fun _ => rfl⟩,
          fun i => toReal (cZ₁.c i) + toReal (cZ₂.c i) - toReal ((cZ₁.plus cZ₂).c i), ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) fun l => ?_
    · rw [Fin.append_left]; exact hβ₁ l
    · rw [Fin.append_right]; exact hβ₂ l
  · -- through `mpr` rather than `rw`: the goal spells the count as
    -- `(cZ₁.plus cZ₂).h`, which is the padding lemma's `cZ₁.h + cZ₂.h` only up to defeq
    refine HPolytope.mem_stackRows_nominal_iff.mpr ⟨HPolytope.mem_padLeft_nominal_iff.mpr ?_,
      HPolytope.mem_padRight_nominal_iff.mpr ?_⟩
    · rw [blockLeft_append]; exact hP₁
    · rw [blockRight_append]; exact hP₂
  · exact Interval.sub_mem_residual fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩
  · funext i
    simp only [Pi.add_apply]
    rw [ConZonotope.aux_sum_univ_plus]
    simp only [ConZonotope.plus, hz₁ i, hz₂ i, Fin.append_left, Fin.append_right]
    ring

theorem ConZonotope.aux_plus_error (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    (I_error cZ₁).construct + (I_error cZ₂).construct
      + (Zonotope.centerResidual cZ₁.c cZ₂.c).construct ⊆ (I_error (cZ₁.plus cZ₂)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_outer cZ₁.I_error cZ₂.I_error))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.plus_outer (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ₁.construct + cZ₂.construct ⊆ (cZ₁.plus cZ₂).construct :=
  InflatedContSet.plus_subset (ConZonotope.aux_plus_nominal cZ₁ cZ₂)
    (ConZonotope.aux_plus_error cZ₁ cZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
