module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.ContSet.Zonotope.Float.Operations.OfIntervalMat
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# `Zonotope.ofIntervalMat` contains the interval matrix

A member's distance from the center is within the entry's radius (`sub_mem_matResidual`),
so the entry's own generator reaches it with coefficient `Zonotope.coefficient`, and no
other generator touches that entry.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ofIntervalMat_outer (I : Interval (Mat 𝕋 m n)) :
    I.construct ⊆ (Zonotope.ofIntervalMat I).construct := by -- --- PROOF ---
  intro X hX
  set C := Interval.centerMat I
  set Rs := Interval.matResidual I.inf I.sup C
  set r : Mat 𝕋 m n := fun i j => maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j))
  set D : Mat ℝ m n := fun i j => X i j - toReal (C i j)
  have hD := Interval.mem_mat_iff.mp
    (Interval.sub_mem_matResidual (stored := C) fun i j => Interval.mem_mat_iff.mp hX i j)
  -- each entry's distance from the center, within that entry's radius
  have hDr : ∀ i j, |D i j| ≤ toReal (r i j) := by
    intro i j
    simp only [r, toReal_maximum, toReal_absolute]
    exact abs_le_max_abs_abs (hD i j).1 (hD i j).2
  set β : Fin (m * n) → ℝ := fun k =>
    CORALean.Real.Zonotope.coefficient (toReal (r (finProdFinEquiv.symm k).1
      (finProdFinEquiv.symm k).2)) (D (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  have hβ : ∀ k, |β k| ≤ 1 := fun k =>
    CORALean.Real.Zonotope.abs_coefficient_le_one (le_trans (abs_nonneg _) (hDr _ _)) (hDr _ _)
  refine ⟨X, ⟨β, hβ, ?_⟩, 0, ?_, add_zero X⟩
  -- only the entry's own generator reaches it
  · funext i j
    show X i j = toReal (C i j) + (∑ k, β k • (Zonotope.ofIntervalMat I).nominal.G k) i j
    rw [Matrix.sum_apply, Finset.sum_eq_single (finProdFinEquiv (i, j))]
    · simp only [realImage_mat, Zonotope.ofIntervalMat, Matrix.smul_apply,
        toRealMat, smul_eq_mul, if_true, β, Equiv.symm_apply_apply]
      rw [mul_comm, CORALean.Real.Zonotope.mul_coefficient (hDr i j)]
      ring
    · intro k _ hk
      simp only [realImage_mat, Zonotope.ofIntervalMat, Matrix.smul_apply,
        toRealMat, smul_eq_mul, if_neg (Ne.symm hk), toReal_zero, mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  · refine Interval.mem_mat_iff.mpr fun i j => ?_
    show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
