module

public import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Operations.CenterResidual
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `Zonotope.plus` over-approximates the Minkowski sum

`InflatedContSet.plus_subset` reduces this to two obligations: the nominal parts
spill only by the center rounding, and the box absorbs that spill along with the
two incoming boxes.

The nominal obligation is the exact `plus` argument — `Fin.append β₁ β₂` as the
witness — with the center displaced; the error obligation is two applications of
`Interval.plus_outer`. The count is therefore still `h + k`, the rounding having
gone into the box.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope

## Hypotheses
* none

## Conclusion
* Minkowski sum is contained in the computed sum
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the projection
because that is the form the goal has and simp will not rewrite a binder's type. -/
private theorem Zonotope.aux_sum_univ_plus {Z₁ Z₂ : Zonotope (Vec 𝕋 n)}
    (f : Fin (Z₁.h + Z₂.h) → ℝ) :
    ∑ j : Fin (Z₁.plus Z₂).h, f j
      = ∑ j, f (Fin.castAdd Z₂.h j) + ∑ j, f (Fin.natAdd Z₁.h j) :=
  Fin.sum_univ_add f

/-- The concatenated generators account for everything but the center rounding. -/
private theorem Zonotope.aux_plus_nominal (Z₁ : Zonotope (Vec 𝕋 n))
    (Z₂ : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    (nominal Z₁).construct + (nominal Z₂).construct ⊆
      (nominal (Z₁.plus Z₂)).construct
        + (Zonotope.centerResidual Z₁.c Z₂.c).construct := by -- --- PROOF ---
  rintro _ ⟨z₁, hz₁', z₂, hz₂', rfl⟩
  obtain ⟨β₁, hβ₁, hz₁⟩ := Zonotope.mem_nominalSet_iff.mp hz₁'
  obtain ⟨β₂, hβ₂, hz₂⟩ := Zonotope.mem_nominalSet_iff.mp hz₂'
  refine ⟨fun i => toReal ((Z₁.plus Z₂).c i)
            + ∑ j, toReal ((Z₁.plus Z₂).G j i) * Fin.append β₁ β₂ j,
          Zonotope.mem_nominalSet_iff.mpr ⟨Fin.append β₁ β₂, ?_, fun _ => rfl⟩,
          fun i => toReal (Z₁.c i) + toReal (Z₂.c i) - toReal ((Z₁.plus Z₂).c i), ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun l => ?_)
    · simpa using hβ₁ l
    · simpa using hβ₂ l
  · exact Interval.sub_mem_residual
      (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  · funext i
    simp only [Pi.add_apply]
    rw [Zonotope.aux_sum_univ_plus]
    simp only [Zonotope.plus, hz₁ i, hz₂ i, Fin.append_left, Fin.append_right]
    ring

/-- The box absorbs the two incoming boxes and the center rounding. -/
private theorem Zonotope.aux_plus_error (Z₁ : Zonotope (Vec 𝕋 n)) (Z₂ : Zonotope (Vec 𝕋 n)) :
    Z₁.I_error.construct + Z₂.I_error.construct + (Zonotope.centerResidual Z₁.c Z₂.c).construct ⊆
      (Z₁.plus Z₂).I_error.construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_outer Z₁.I_error Z₂.I_error))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.plus_outer (Z₁ : Zonotope (Vec 𝕋 n)) (Z₂ : Zonotope (Vec 𝕋 n)) :
    Z₁.construct + Z₂.construct ⊆ (Z₁.plus Z₂).construct :=
  InflatedContSet.plus_subset (Zonotope.aux_plus_nominal Z₁ Z₂) (Zonotope.aux_plus_error Z₁ Z₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
