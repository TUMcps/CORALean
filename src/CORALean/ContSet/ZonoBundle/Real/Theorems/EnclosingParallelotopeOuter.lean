module

public import CORALean.ContSet.ZonoBundle.Real.Operations.EnclosingParallelotope
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalAllContains
public import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesOuter
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `ZonoBundle.enclosingParallelotope` over-approximates the bundle

`Γ⁻¹` carries the bundle into the box, `Γ` carries the box back, and the two cancel at an
invertible `Γ`: the same argument as `Zonotope.parallelotope_outer`, at the box of the whole
bundle.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped Classical

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.enclosingParallelotope_outer (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (Γ : Mat ℝ n n) :
    zB.construct ⊆ (zB.enclosingParallelotope hk Γ).construct := by -- --- PROOF ---
  -- the directions actually used are invertible
  obtain ⟨Γ', hΓ', hdef⟩ : ∃ Γ' : Mat ℝ n n, IsUnit Γ'.det ∧
      zB.enclosingParallelotope hk Γ
        = ZonoBundle.parallelotope Γ' ((zB.mtimes Γ'⁻¹).intervalAll hk) := by
    by_cases h : IsUnit Γ.det
    · exact ⟨Γ, h, by simp only [ZonoBundle.enclosingParallelotope, if_pos h]⟩
    · exact ⟨1, by simp, by simp only [ZonoBundle.enclosingParallelotope, if_neg h]⟩
  rw [hdef]
  intro x hx
  -- `Γ'⁻¹ x` lies in the mapped bundle, hence in its box
  have hbox := Interval.zonotope_contains _
    (ZonoBundle.intervalAll_contains (zB.mtimes Γ'⁻¹) hk
      (ZonoBundle.mtimes_outer Γ'⁻¹ zB ⟨x, hx, rfl⟩))
  -- and `Γ'` maps it back to `x`
  rw [ZonoBundle.parallelotope, ← Zonotope.mtimes_exact]
  refine ⟨_, hbox, ?_⟩
  show Γ' *ᵥ (Γ'⁻¹ *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hΓ', Matrix.one_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
