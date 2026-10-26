module

public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.ContSet.Zonotope.Float.Operations.OfEntryBoundsMat
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# `Zonotope.ofEntryBoundsMat` contains the exact matrix zonotope it brackets

The exact zonotope's coefficients are the witness, unchanged: the stored generators
reach the nominal part, and what they miss — the center's gap and each generator's gap
times its coefficient — lands in the box, the second within the summed widths because
every gap is nonnegative and below its width.

## Inputs
* `Z` – exact matrix zonotope
* `cLo` – lower center bounds
* `cHi` – upper center bounds
* `GLo` – lower generator bounds
* `GHi` – upper generator bounds
* `E` – error box

## Hypotheses
* `hc` – center within its bounds
* `hG` – generators within their bounds

## Conclusion
* exact zonotope plus box is contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The generators' gaps, scaled by coefficients in `[-1, 1]`, within the summed widths. -/
private theorem Zonotope.aux_abs_gap_le {h : ℕ} {GLo GHi : Fin h → Mat 𝕋 m n}
    {G : Fin h → Mat ℝ m n}
    (hG : ∀ k i j, toReal (GLo k i j) ≤ G k i j ∧ G k i j ≤ toReal (GHi k i j))
    {β : Fin h → ℝ} (hβ : ∀ k, |β k| ≤ 1) (i : Fin m) (j : Fin n) : -- --- CONCL ---
    |∑ k, β k * (G k i j - toReal (GLo k i j))|
      ≤ toReal (sumUp fun k => subUp (GHi k i j) (GLo k i j)) := by -- --- PROOF ---
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sum_le_sumUp _))
  refine Finset.sum_le_sum fun k _ => ?_
  have h0 : 0 ≤ G k i j - toReal (GLo k i j) := sub_nonneg.mpr (hG k i j).1
  -- the gap never exceeds the width, and the coefficient never exceeds one
  have hw : G k i j - toReal (GLo k i j) ≤ toReal (subUp (GHi k i j) (GLo k i j)) :=
    le_trans (sub_le_sub_right (hG k i j).2 _) (sub_le_subUp _ _)
  rw [abs_mul, abs_of_nonneg h0]
  exact le_trans (mul_le_of_le_one_left h0 (hβ k)) hw


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ofEntryBoundsMat_outer (Z : CORALean.Real.Zonotope (Mat ℝ m n))
    {cLo cHi : Mat 𝕋 m n} {GLo GHi : Fin Z.h → Mat 𝕋 m n} (E : Interval (Mat 𝕋 m n))
    (hc : ∀ i j, toReal (cLo i j) ≤ Z.c i j ∧ Z.c i j ≤ toReal (cHi i j))
    (hG : ∀ k i j, toReal (GLo k i j) ≤ Z.G k i j ∧ Z.G k i j ≤ toReal (GHi k i j))
    : -- --- CONCL ---
    Z.construct + E.construct
      ⊆ (Zonotope.ofEntryBoundsMat cLo cHi GLo GHi E).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨β, hβ, rfl⟩, e, he, rfl⟩
  set gap : Mat ℝ m n := fun i j => ∑ k, β k * (Z.G k i j - toReal (GLo k i j))
  set dc : Mat ℝ m n := fun i j => Z.c i j - toReal (cLo i j)
  refine ⟨toRealMat cLo + ∑ k, β k • toRealMat (GLo k), ⟨β, hβ, rfl⟩, e + dc + gap,
    Interval.matPlus_outer _ _ (Interval.matPlus_outer _ _ he
      (Interval.sub_mem_matResidual fun i j => hc i j)) ?_, ?_⟩
  -- the generators' share: a symmetric box of the summed widths
  · refine Interval.mem_mat_iff.mpr fun i j => ?_
    have hb := abs_le.mp (Zonotope.aux_abs_gap_le hG hβ i j)
    refine ⟨?_, hb.2⟩
    show toReal (neg _) ≤ _
    rw [toReal_neg]
    exact hb.1
  -- entry by entry, the stored part and the gaps recombine into the exact point
  · funext i j
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, gap, dc]
    have hsum : ∑ k, β k * Z.G k i j
        = ∑ k, β k * toRealMat (GLo k) i j + ∑ k, β k * (Z.G k i j - toReal (GLo k i j)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [toRealMat]; ring
    rw [hsum]
    simp only [toRealMat]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
