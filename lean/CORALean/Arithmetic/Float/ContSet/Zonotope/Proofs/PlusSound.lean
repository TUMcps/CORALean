import CORALean.Arithmetic.Float.ContSet.Zonotope.API

/-!
# `Zonotope.plus` over-approximates the Minkowski sum

`InflatedContSet.plus_subset` reduces this to two obligations, and the split is
exactly the design: the nominal parts spill only by the centre rounding, and the
box absorbs that spill along with the two incoming boxes.

The nominal obligation is the exact `plus` argument — `Fin.append β₁ β₂` as the
witness — with the centre displaced. The error obligation is two applications of
`Interval.plus_sound` and nothing else.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Zonotope.Proofs

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n h k : ℕ}

/-- The concatenated generators account for everything but the centre rounding. -/
theorem plus_nominal (Z₁ : Zonotope F n h) (Z₂ : Zonotope F n k) :
    (nominal Z₁).construct + (nominal Z₂).construct ⊆
      (nominal (Z₁.plus Z₂)).construct + (Zonotope.centerResidual Z₁.c Z₂.c).construct := by
  rintro _ ⟨z₁, ⟨β₁, hβ₁, hz₁⟩, z₂, ⟨β₂, hβ₂, hz₂⟩, rfl⟩
  refine ⟨fun i => toReal ((Z₁.plus Z₂).c i)
            + ∑ j, toReal ((Z₁.plus Z₂).G i j) * Fin.append β₁ β₂ j,
          ⟨Fin.append β₁ β₂, ?_, fun _ => rfl⟩,
          fun i => toReal (Z₁.c i) + toReal (Z₂.c i) - toReal ((Z₁.plus Z₂).c i), ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun l => ?_)
    · simpa using hβ₁ l
    · simpa using hβ₂ l
  · exact Interval.sub_mem_residual
      (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  · funext i
    simp only [Zonotope.plus, Zonotope.nominal_c, Zonotope.nominal_G, toRealMat, toRealVec, Pi.add_apply, hz₁ i, hz₂ i,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    ring

/-- The box absorbs the two incoming boxes and the centre rounding. -/
theorem plus_error (Z₁ : Zonotope F n h) (Z₂ : Zonotope F n k) :
    Z₁.E.construct + Z₂.E.construct + (Zonotope.centerResidual Z₁.c Z₂.c).construct ⊆
      (Z₁.plus Z₂).E.construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_sound Z₁.E Z₂.E))
    (Interval.plus_sound _ _)

theorem plus_sound (Z₁ : Zonotope F n h) (Z₂ : Zonotope F n k) :
    Z₁.construct + Z₂.construct ⊆ (Z₁.plus Z₂).construct :=
  InflatedContSet.plus_subset (plus_nominal Z₁ Z₂) (plus_error Z₁ Z₂)

end CORALean.Arithmetic.Float.Zonotope.Proofs
