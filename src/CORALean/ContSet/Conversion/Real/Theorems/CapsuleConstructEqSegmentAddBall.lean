module

public import CORALean.ContSet.Capsule.Real.Theorems.MemConstructIffNorm
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# A capsule is its segment plus its ball

CORA builds `spectraShadow(C)` and `conPolyZono(C)` as `zonotope(c, g)` plus the ball
`ellipsoid(r² I)`, both exact; this is why. The ball is `ellipsoid(r² I)` as CORALean writes it,
`Ellipsoid.ofFactor (r • 1) 0`, the points `r u` with `‖u‖₂ ≤ 1`. A nonnegative radius is needed:
a negative one is CORALean's empty capsule, while `r² I` is the ball of radius `|r|`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A capsule of nonnegative radius is `zonotope(c, g)` plus `ellipsoid(r² I)`. -/
theorem Capsule.construct_eq_segment_add_ball (C : Capsule n) (hr : 0 ≤ C.r) :
    C.construct = (⟨1, C.c, fun _ => C.g⟩ : Zonotope (Vec ℝ n)).construct
      + (Ellipsoid.ofFactor (C.r • (1 : Mat ℝ n n)) 0).construct := by -- --- PROOF ---
  ext x
  rw [Capsule.mem_construct_iff_norm₂, Ellipsoid.construct_ofFactor, Set.mem_add]
  constructor
  · rintro ⟨t, ht, hle⟩
    -- `y`, what the segment point leaves, is `r` times a vector of the unit ball
    set y : Vec ℝ n := (x - C.c) - t • C.g with hy
    rcases hr.lt_or_eq with hpos | hzero
    · refine ⟨C.c + t • C.g, ⟨fun _ => t, fun _ => abs_le.mpr ht, by simp⟩,
        0 + (C.r • (1 : Mat ℝ n n)) *ᵥ (C.r⁻¹ • y), ⟨C.r⁻¹ • y, ?_, rfl⟩, ?_⟩
      · rw [norm₂_smul, abs_of_pos (inv_pos.mpr hpos)]
        calc C.r⁻¹ * ‖y‖₂ ≤ C.r⁻¹ * C.r := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hr)
          _ = 1 := inv_mul_cancel₀ hpos.ne'
      · rw [zero_add, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ hpos.ne',
          one_smul, hy]
        abel
    -- no radius: `y = 0`, the segment point is `x`
    · have hy0 : y = 0 := by
        rw [← hzero] at hle
        have h := le_antisymm hle (norm₂_nonneg y)
        rw [← norm_toEuclidean, norm_eq_zero, map_eq_zero_iff _ toEuclidean.injective] at h
        exact h
      refine ⟨C.c + t • C.g, ⟨fun _ => t, fun _ => abs_le.mpr ht, by simp⟩,
        0 + (C.r • (1 : Mat ℝ n n)) *ᵥ 0, ⟨0, by rw [norm₂_zero]; exact zero_le_one, rfl⟩, ?_⟩
      rw [Matrix.mulVec_zero, add_zero, add_zero]
      rw [hy, sub_sub, sub_eq_zero] at hy0
      exact hy0.symm
  -- back: the segment coefficient is `t`, and `‖r u‖₂ = r ‖u‖₂ ≤ r`
  · rintro ⟨s, ⟨β, hβ, rfl⟩, b, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨β 0, abs_le.mp (hβ 0), ?_⟩
    have hx : (C.c + ∑ j, β j • C.g) + (0 + (C.r • (1 : Mat ℝ n n)) *ᵥ u) - C.c - β 0 • C.g
        = C.r • u := by
      rw [Fin.sum_univ_one, zero_add, Matrix.smul_mulVec, Matrix.one_mulVec]
      abel
    rw [hx, norm₂_smul, abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr hu

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
