import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.SpectraShadow.Float.Operations.Plus
import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero
import CORALean.ContSet.SpectraShadow.Real.Theorems.LmiAppend
import CORALean.ContSet.SpectraShadow.Real.Theorems.PosSemidefPlusIff

/-!
# `SpectraShadow.plus` over-approximates the Minkowski sum

`InflatedContSet.plus_subset` reduces this to two obligations: the nominal parts
spill only by the centre rounding, and the box absorbs that spill along with the
two incoming boxes.

The nominal obligation is the exact `plus` argument — `Fin.append β₁ β₂` as the
witness, the inequality splitting along the diagonal into the two it came from —
with the centre displaced; the error obligation is two applications of
`Interval.plus_outer`. The sizes are therefore still `k₁ + k₂` and `m₁ + m₂`, the
rounding having gone into the box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s variable count, stated through the projection
because that is the form the goal has and simp will not rewrite a binder's type. -/
theorem SpectraShadow.aux_sum_append {S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)}
    (f : Fin (S₁.m + S₂.m) → ℝ) :
    ∑ j : Fin (S₁.plus S₂).m, f j
      = ∑ j, f (Fin.castAdd S₂.m j) + ∑ j, f (Fin.natAdd S₁.m j) :=
  Fin.sum_univ_add f

/-- The stored inequality of the sum holds exactly when both inequalities do. -/
theorem SpectraShadow.aux_posSemidef_plus (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n))
    (β : Fin (S₁.m + S₂.m) → ℝ) :
    (toRealMat (S₁.plus S₂).A₀ + ∑ i : Fin (S₁.plus S₂).m, β i • toRealMat ((S₁.plus S₂).A i)
      ).PosSemidef
      ↔ (toRealMat S₁.A₀ + ∑ i, β (Fin.castAdd S₂.m i) • toRealMat (S₁.A i)).PosSemidef
        ∧ (toRealMat S₂.A₀ + ∑ j, β (Fin.natAdd S₁.m j) • toRealMat (S₂.A j)).PosSemidef
    := by -- --- PROOF ---
  have hA : ∀ i : Fin (S₁.m + S₂.m), toRealMat ((S₁.plus S₂).A i)
      = (Fin.append (fun i => blockDiag 0 (toRealMat (S₁.A i)) 0)
          (fun j => blockDiag 0 0 (toRealMat (S₂.A j)))
          : Fin (S₁.m + S₂.m) → Mat ℝ (S₁.k + S₂.k) (S₁.k + S₂.k)) i := by
    intro i
    refine Fin.addCases (fun p => ?_) (fun p => ?_) i
    · simp only [SpectraShadow.plus, Fin.append_left, SpectraShadow.toRealMat_blockDiag,
        SpectraShadow.toRealMat_const_zero]
    · simp only [SpectraShadow.plus, Fin.append_right, SpectraShadow.toRealMat_blockDiag,
        SpectraShadow.toRealMat_const_zero]
  have h₀ : toRealMat (S₁.plus S₂).A₀ = blockDiag 0 (toRealMat S₁.A₀) (toRealMat S₂.A₀) :=
    SpectraShadow.toRealMat_blockDiag _ _
  have e : toRealMat (S₁.plus S₂).A₀ + ∑ i : Fin (S₁.plus S₂).m, β i • toRealMat ((S₁.plus S₂).A i)
      = blockDiag 0 (toRealMat S₁.A₀ + ∑ i, β (Fin.castAdd S₂.m i) • toRealMat (S₁.A i))
          (toRealMat S₂.A₀ + ∑ j, β (Fin.natAdd S₁.m j) • toRealMat (S₂.A j)) := by
    rw [h₀, Finset.sum_congr rfl fun i _ => by rw [hA i]]
    exact Real.SpectraShadow.lmi_append _ _ _ _ β
  exact (Iff.of_eq (congrArg Matrix.PosSemidef e)).trans (posSemidef_blockDiag_iff _ _)

/-- The concatenated generators account for everything but the centre rounding. -/
theorem SpectraShadow.aux_plus_nominal (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    (nominalSet S₁) + (nominalSet S₂) ⊆
      (nominalSet (S₁.plus S₂))
        + (SpectraShadow.centerResidual S₁.c S₂.c).construct := by -- --- PROOF ---
  rintro _ ⟨z₁, hz₁', z₂, hz₂', rfl⟩
  obtain ⟨β₁, hP₁, hz₁⟩ := SpectraShadow.mem_nominalSet_iff.mp hz₁'
  obtain ⟨β₂, hP₂, hz₂⟩ := SpectraShadow.mem_nominalSet_iff.mp hz₂'
  refine ⟨fun i => toReal ((S₁.plus S₂).c i)
            + ∑ j, toReal ((S₁.plus S₂).G j i) * Fin.append β₁ β₂ j,
          SpectraShadow.mem_nominalSet_iff.mpr
            ⟨Fin.append β₁ β₂, ?_, fun _ => rfl⟩,
          fun i => toReal (S₁.c i) + toReal (S₂.c i) - toReal ((S₁.plus S₂).c i), ?_, ?_⟩
  · refine (SpectraShadow.aux_posSemidef_plus S₁ S₂ (Fin.append β₁ β₂)).mpr ?_
    simpa using ⟨hP₁, hP₂⟩
  · exact Interval.sub_mem_residual
      (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  · funext i
    simp only [Pi.add_apply]
    rw [SpectraShadow.aux_sum_append]
    simp only [SpectraShadow.plus, hz₁ i, hz₂ i, Fin.append_left, Fin.append_right]
    ring

/-- The box absorbs the two incoming boxes and the centre rounding. -/
theorem SpectraShadow.aux_plus_error (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    S₁.E.construct + S₂.E.construct + (SpectraShadow.centerResidual S₁.c S₂.c).construct ⊆
      (S₁.plus S₂).E.construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_outer S₁.E S₂.E))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.plus_outer (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    S₁.construct + S₂.construct ⊆ (S₁.plus S₂).construct :=
  InflatedContSet.plus_subset (SpectraShadow.aux_plus_nominal S₁ S₂)
    (SpectraShadow.aux_plus_error S₁ S₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
