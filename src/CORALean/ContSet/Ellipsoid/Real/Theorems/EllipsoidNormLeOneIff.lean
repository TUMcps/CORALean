module

public import CORALean.ContSet.Ellipsoid.Real.Operations.EllipsoidNorm
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsUnitShape
public import CORALean.ContSet.Ellipsoid.Real.Operations.Rank

@[expose] public section

/-!
# The ellipsoid norm is the ellipsoid's gauge

For a full-rank ellipsoid, `ellipsoidNorm E p ≤ 1` exactly when the translate `q + p` of the point
lies in the ellipsoid: `ellipsoidNorm` is the smallest `‖u‖₂` with `G u = p`, attained at the
minimum-norm solution `u = Gᵀ (G Gᵀ)⁻¹ p`, for which `|pᵀ (G Gᵀ)⁻¹ p| = ‖u‖₂²`. Any other
solution differs from it by a kernel vector of `G`, which is orthogonal to `u`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.ellipsoidNorm_le_one_iff (E : Ellipsoid n) (hr : E.rank = n) (p : Vec ℝ n) :
    E.ellipsoidNorm p ≤ 1 ↔ E.q + p ∈ E.construct := by -- --- PROOF ---
  have hU := E.isUnit_shape hr
  -- the minimum-norm solution `u = Gᵀ Q⁻¹ p` of `G u = p`
  set w : Vec ℝ n := E.shape⁻¹ *ᵥ p with hw
  set u : Vec ℝ E.k := E.Gᵀ *ᵥ w with hu
  have hSw : E.shape *ᵥ w = p := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
  have hGu : E.G *ᵥ u = p := by
    rw [hu, Matrix.mulVec_mulVec]
    exact hSw
  have huu : u ⬝ᵥ u = p ⬝ᵥ w :=
    calc u ⬝ᵥ u = (E.Gᵀ *ᵥ w) ⬝ᵥ u := rfl
      _ = w ⬝ᵥ (E.G *ᵥ u) := Ellipsoid.dot_transpose _ _ _
      _ = p ⬝ᵥ w := by rw [hGu, dotProduct_comm]
  -- the norm is that of the minimum-norm solution
  have hnorm : E.ellipsoidNorm p = ‖u‖₂ := by
    unfold Ellipsoid.ellipsoidNorm
    simp only
    rw [← hw, ← huu, dotProduct_self, abs_of_nonneg (sq_nonneg _)]
    exact Real.sqrt_sq (norm₂_nonneg u)
  rw [hnorm]
  constructor
  · -- `u` itself reaches the translated point
    intro h
    exact ⟨u, h, by rw [hGu]⟩
  · rintro ⟨u', hu', hx⟩
    have hp : E.G *ᵥ u' = p := (add_left_cancel hx).symm
    -- `u' = u + v` with `G v = 0`, and `v` orthogonal to `u`
    set v := u' - u with hv
    have hGv : E.G *ᵥ v = 0 := by rw [hv, Matrix.mulVec_sub, hp, hGu, sub_self]
    have huv : u ⬝ᵥ v = 0 := by
      rw [hu, Ellipsoid.dot_transpose, hGv, dotProduct_zero]
    have hsplit : u' ⬝ᵥ u' = u ⬝ᵥ u + 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
      have : u' = u + v := by rw [hv]; abel
      rw [this, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm v u]
      ring
    have hvv : 0 ≤ ‖v‖₂ ^ 2 := sq_nonneg _
    rw [dotProduct_self u', dotProduct_self u, dotProduct_self v, huv] at hsplit
    have hu'1 : ‖u'‖₂ ^ 2 ≤ 1 := by nlinarith [norm₂_nonneg u']
    have hsq : ‖u‖₂ ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm₂_nonneg u]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
