import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.LevelSet.Real.LevelSet

/-!
# An ellipsoid as a level set

CORA's `levelSet(ellipsoid)`: `(x - q)ᵀ Q⁻¹ (x - q) - 1 ≤ 0`, with `Q` the shape matrix. The
ellipsoid stores a generator matrix `G`, so `Q = G Gᵀ`. CORA's `inv(E.Q)` presumes `Q`
invertible, and so does the equality below (`G` of full row rank); a degenerate ellipsoid is not
a sublevel set of this quadratic form, and the conversion is not claimed for it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix CORALean

variable {n : ℕ}


/-- `levelSet(E)`: the single constraint `(x - q)ᵀ (G Gᵀ)⁻¹ (x - q) - 1 ≤ 0`. -/
noncomputable def Ellipsoid.levelSet (E : Ellipsoid n) : LevelSet n where
  m := 1
  f x := fun _ => (x - E.q) ⬝ᵥ ((E.G * E.Gᵀ)⁻¹ *ᵥ (x - E.q)) - 1
  op := fun _ => .le


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.levelSet_exact (E : Ellipsoid n) (hQ : IsUnit (E.G * E.Gᵀ).det) :
    E.levelSet.construct = E.construct := by -- --- PROOF ---
  set Q := E.G * E.Gᵀ with hQdef
  -- through `w = Q⁻¹ y`: `G (Gᵀ w) = y`, and the vector `Gᵀ w` has squared length `yᵀ Q⁻¹ y`
  have hQw : ∀ y : Vec ℝ n, E.G *ᵥ (E.Gᵀ *ᵥ (Q⁻¹ *ᵥ y)) = y := fun y => by
    rw [Matrix.mulVec_mulVec]
    simp [← hQdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ]
  -- the squared length of `Gᵀ w`, and its inner product with any `u` mapped to `y` by `G`
  have hz : ∀ y : Vec ℝ n, (E.Gᵀ *ᵥ (Q⁻¹ *ᵥ y)) ⬝ᵥ (E.Gᵀ *ᵥ (Q⁻¹ *ᵥ y)) =
      y ⬝ᵥ (Q⁻¹ *ᵥ y) := fun y => by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hQw, dotProduct_comm]
  have hzu : ∀ (y : Vec ℝ n) (u : Vec ℝ E.k), E.G *ᵥ u = y →
      (E.Gᵀ *ᵥ (Q⁻¹ *ᵥ y)) ⬝ᵥ u = y ⬝ᵥ (Q⁻¹ *ᵥ y) := fun y u hu => by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hu, dotProduct_comm]
  ext x
  constructor
  -- a point of the sublevel set is `q + G u` for `u = Gᵀ Q⁻¹ (x - q)`, of squared length `≤ 1`
  · intro h
    have h1 : (x - E.q) ⬝ᵥ (Q⁻¹ *ᵥ (x - E.q)) ≤ 1 := by
      have := h (0 : Fin 1)
      simp only [Ellipsoid.levelSet, CompOp.holds] at this
      linarith
    refine ⟨E.Gᵀ *ᵥ (Q⁻¹ *ᵥ (x - E.q)), ?_, ?_⟩
    · rw [← pow_le_one_iff_of_nonneg (norm₂_nonneg _) two_ne_zero, ← dotProduct_self, hz]
      exact h1
    · rw [hQw]; abel
  -- conversely `‖z - u‖² ≥ 0` for `z = Gᵀ Q⁻¹ y` gives `yᵀ Q⁻¹ y ≤ ‖u‖² ≤ 1`
  · rintro ⟨u, hu, rfl⟩ i
    simp only [Ellipsoid.levelSet, CompOp.holds, add_sub_cancel_left]
    set y := E.G *ᵥ u with hy
    have h2 : ‖u‖₂ ^ 2 ≤ 1 := by
      have := norm₂_nonneg u
      nlinarith
    have h3 : 0 ≤ (E.Gᵀ *ᵥ (Q⁻¹ *ᵥ y) - u) ⬝ᵥ (E.Gᵀ *ᵥ (Q⁻¹ *ᵥ y) - u) := by
      rw [dotProduct_self]; positivity
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hz, hzu y u hy.symm,
      dotProduct_comm u, hzu y u hy.symm, dotProduct_self] at h3
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
