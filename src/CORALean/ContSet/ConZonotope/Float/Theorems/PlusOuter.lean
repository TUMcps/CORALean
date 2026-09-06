import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.ConZonotope.Float.Operations.Plus
import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# `ConZonotope.plus` over-approximates the Minkowski sum

The zonotope's argument with one step added, and that step costs nothing: the
concatenated coefficients satisfy the padded constraints exactly when each half
satisfies its own, which is `mem_and_iff` composed with `blockLeft_append`. Only
the centre rounds, and its residual is what the box absorbs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the projection
because that is the form the goal has. -/
theorem ConZonotope.aux_sum_univ_plus {C₁ C₂ : ConZonotope 𝕋 n} (f : Fin (C₁.h + C₂.h) → ℝ) :
    ∑ j : Fin (C₁.plus C₂).h, f j
      = ∑ j, f (Fin.castAdd C₂.h j) + ∑ j, f (Fin.natAdd C₁.h j) :=
  Fin.sum_univ_add f

theorem ConZonotope.aux_plus_nominal (C₁ C₂ : ConZonotope 𝕋 n) :
    nominalSet C₁ + nominalSet C₂ ⊆
      nominalSet (C₁.plus C₂) + (Zonotope.centerResidual C₁.c C₂.c).construct := by -- --- PROOF ---
  rintro _ ⟨z₁, hz₁', z₂, hz₂', rfl⟩
  obtain ⟨β₁, hβ₁, hP₁, hz₁⟩ := ConZonotope.mem_nominalSet_iff.mp hz₁'
  obtain ⟨β₂, hβ₂, hP₂, hz₂⟩ := ConZonotope.mem_nominalSet_iff.mp hz₂'
  refine ⟨fun i => toReal ((C₁.plus C₂).c i)
            + ∑ j, toReal ((C₁.plus C₂).G i j) * Fin.append β₁ β₂ j,
          ConZonotope.mem_nominalSet_iff.mpr ⟨Fin.append β₁ β₂, ?_, ?_, fun _ => rfl⟩,
          fun i => toReal (C₁.c i) + toReal (C₂.c i) - toReal ((C₁.plus C₂).c i), ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) fun l => ?_
    · rw [Fin.append_left]; exact hβ₁ l
    · rw [Fin.append_right]; exact hβ₂ l
  · -- through `mpr` rather than `rw`: the goal spells the count as
    -- `(C₁.plus C₂).h`, which is the padding lemma's `C₁.h + C₂.h` only up to defeq
    refine HPolytope.mem_and_iff.mpr ⟨HPolytope.mem_padLeft_iff.mpr ?_,
      HPolytope.mem_padRight_iff.mpr ?_⟩
    · rw [blockLeft_append]; exact hP₁
    · rw [blockRight_append]; exact hP₂
  · exact Interval.sub_mem_residual fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩
  · funext i
    simp only [Pi.add_apply]
    rw [ConZonotope.aux_sum_univ_plus]
    simp only [ConZonotope.plus, hz₁ i, hz₂ i, Fin.append_left, Fin.append_right]
    ring

theorem ConZonotope.aux_plus_error (C₁ C₂ : ConZonotope 𝕋 n) :
    (error C₁).construct + (error C₂).construct
      + (Zonotope.centerResidual C₁.c C₂.c).construct ⊆ (error (C₁.plus C₂)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_outer C₁.E C₂.E))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.plus_outer (C₁ C₂ : ConZonotope 𝕋 n) :
    C₁.construct + C₂.construct ⊆ (C₁.plus C₂).construct :=
  InflatedContSet.plus_subset (ConZonotope.aux_plus_nominal C₁ C₂)
    (ConZonotope.aux_plus_error C₁ C₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
