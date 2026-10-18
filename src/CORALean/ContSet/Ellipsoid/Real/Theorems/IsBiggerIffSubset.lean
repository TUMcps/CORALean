module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Operations.IsBigger
public import CORALean.ContSet.Ellipsoid.Real.Theorems.EllipsoidNormLeOneIff
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsUnitShape
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose

@[expose] public section

/-!
# `isBigger` is containment of the centered ellipsoids

For `E₁` of full rank, `Q₂ ⪯ Q₁` holds iff `E₂ - q₂ ⊆ E₁ - q₁`.
Containment gives `‖G₂ᵀ v‖ ≤ ‖G₁ᵀ v‖` for every `v` through the support point `G₂ G₂ᵀ v`
(`vᵀ Q v = ‖Gᵀ v‖²`). Conversely, for `x = G₂ u` and `w = Q₁⁻¹ x`, `s = xᵀ w` satisfies
`s ≤ ‖G₂ᵀ w‖` and `‖G₂ᵀ w‖² = wᵀ Q₂ w ≤ wᵀ Q₁ w = s`, so `s ≤ 1`, which is
`ellipsoidNorm ≤ 1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_quad_eq_norm_sq (E : Ellipsoid n) (v : Vec ℝ n) :
    v ⬝ᵥ (E.Q *ᵥ v) = ‖E.Gᵀ *ᵥ v‖₂ ^ 2 := by
  rw [← dotProduct_self, Ellipsoid.dot_transpose, ← E.G_mul_transpose, ← Matrix.mulVec_mulVec]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isBigger_iff_subset (E₁ E₂ : Ellipsoid n) (hr : E₁.rank = n) :
    E₁.isBigger E₂ ↔
      (fun x => x - E₂.q) '' E₂.construct ⊆
        (fun x => x - E₁.q) '' E₁.construct := by -- --- PROOF ---
  rw [E₁.construct_eq_sqrt, E₂.construct_eq_sqrt]
  constructor
  · rintro h _ ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    -- the centered point `p = G₂ u`
    simp only [add_sub_cancel_left]
    set p : Vec ℝ n := E₂.G *ᵥ u with hp
    have hU := E₁.isUnit_shape hr
    set w : Vec ℝ n := E₁.Q⁻¹ *ᵥ p with hw
    have hQw : E₁.Q *ᵥ w = p := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
    -- `s = pᵀ w` is `‖G₁ᵀ w‖²`, and `s ≤ ‖G₂ᵀ w‖ ≤ sqrt s`
    have hs : p ⬝ᵥ w = ‖E₁.Gᵀ *ᵥ w‖₂ ^ 2 := by
      rw [← Ellipsoid.aux_quad_eq_norm_sq, hQw, dotProduct_comm]
    have hs2 : p ⬝ᵥ w ≤ ‖E₂.Gᵀ *ᵥ w‖₂ :=
      calc p ⬝ᵥ w = (E₂.Gᵀ *ᵥ w) ⬝ᵥ u := by
            rw [Ellipsoid.dot_transpose, dotProduct_comm]
        _ ≤ ‖E₂.Gᵀ *ᵥ w‖₂ * ‖u‖₂ := dotProduct_le_norm₂_mul_norm₂ _ _
        _ ≤ ‖E₂.Gᵀ *ᵥ w‖₂ * 1 := mul_le_mul_of_nonneg_left hu (norm₂_nonneg _)
        _ = _ := mul_one _
    have hs3 : ‖E₂.Gᵀ *ᵥ w‖₂ ^ 2 ≤ p ⬝ᵥ w := by
      rw [← Ellipsoid.aux_quad_eq_norm_sq, hs, ← Ellipsoid.aux_quad_eq_norm_sq]
      exact h w
    have hs0 : 0 ≤ p ⬝ᵥ w := by rw [hs]; positivity
    have hle : p ⬝ᵥ w ≤ 1 := by nlinarith
    -- so the centered point is in `E₁ - q₁`
    refine ⟨E₁.q + p, ?_, add_sub_cancel_left _ _⟩
    rw [← E₁.construct_eq_sqrt]
    refine (E₁.ellipsoidNorm_le_one_iff hr p).mp ?_
    unfold Ellipsoid.ellipsoidNorm
    simp only
    rw [← hw, abs_of_nonneg hs0]
    calc Real.sqrt (p ⬝ᵥ w) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  · intro hsub v
    rw [Ellipsoid.aux_quad_eq_norm_sq, Ellipsoid.aux_quad_eq_norm_sq]
    by_cases ha : ‖E₂.Gᵀ *ᵥ v‖₂ = 0
    · rw [ha, zero_pow two_ne_zero]; exact sq_nonneg _
    · have hpos : 0 < ‖E₂.Gᵀ *ᵥ v‖₂ := lt_of_le_of_ne (norm₂_nonneg _) (Ne.symm ha)
      -- the support point of `E₂ - q₂` in direction `v`
      set u : Vec ℝ n := ‖E₂.Gᵀ *ᵥ v‖₂⁻¹ • (E₂.Gᵀ *ᵥ v) with hu
      have hun : ‖u‖₂ = 1 := by
        rw [hu, norm₂_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ ha]
      obtain ⟨_, ⟨u', hu', rfl⟩, hy⟩ := hsub ⟨E₂.q + E₂.G *ᵥ u, ⟨u, hun.le, rfl⟩,
        add_sub_cancel_left _ _⟩
      have hGu : E₁.G *ᵥ u' = E₂.G *ᵥ u := by simpa using hy
      -- `a = vᵀ G₂ u` on one side, at most `‖G₁ᵀ v‖` on the other
      have h1 : ‖E₂.Gᵀ *ᵥ v‖₂ = v ⬝ᵥ (E₂.G *ᵥ u) := by
        rw [← Ellipsoid.dot_transpose, hu, dotProduct_smul, dotProduct_self, smul_eq_mul]
        field_simp
      have h2 : v ⬝ᵥ (E₁.G *ᵥ u') ≤ ‖E₁.Gᵀ *ᵥ v‖₂ :=
        calc v ⬝ᵥ (E₁.G *ᵥ u') = (E₁.Gᵀ *ᵥ v) ⬝ᵥ u' := (Ellipsoid.dot_transpose _ _ _).symm
          _ ≤ ‖E₁.Gᵀ *ᵥ v‖₂ * ‖u'‖₂ := dotProduct_le_norm₂_mul_norm₂ _ _
          _ ≤ ‖E₁.Gᵀ *ᵥ v‖₂ * 1 := mul_le_mul_of_nonneg_left hu' (norm₂_nonneg _)
          _ = _ := mul_one _
      rw [hGu, ← h1] at h2
      exact pow_le_pow_left₀ hpos.le h2 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
