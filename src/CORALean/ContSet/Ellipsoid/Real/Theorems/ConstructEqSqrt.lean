module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsPinvQpinv

@[expose] public section

/-!
# The ellipsoid is the image of the unit ball under the square root

The definition states [1, Def. 4] over the shape matrix,
`{x | (x - q)ᵀ Q⁺ (x - q) ≤ 1, x - q ∈ range Q}`; this is the same set as
`{q + G u | ‖u‖₂ ≤ 1}`, `G = Q^(1/2)`, for every positive semi-definite `Q`, degenerate ones
included. It is the form most proofs go through: convexity, compactness and every exact image are
statements about an affine image of a ball.

Why: `Q⁺` (here `P`) is symmetric, being the pseudo-inverse of a symmetric matrix, and
`R = G P G` fixes the range of `G` (`R G = G`, as `G (R G - G) = Q P Q - Q = 0` and `R G - G`
lies in the range of `G`) and is symmetric and idempotent. A point `y = G u` is then
`Q (P G u)`, in the range of `Q`, and `yᵀ P y = uᵀ R u = ‖R u‖₂² ≤ ‖u‖₂²`. Conversely `y = Q w` is
`G u` for `u = G P y`, of squared length `yᵀ P Q P y = yᵀ P y`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The pseudo-inverse of a symmetric matrix is symmetric: its transpose meets the same four
conditions. -/
private theorem aux_pinv_transpose {Q P : Mat ℝ n n} (hQ : Qᵀ = Q) (hP : IsPinv Q P) :
    Pᵀ = P := by -- --- PROOF ---
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine IsPinv.unique ⟨?_, ?_, ?_, ?_⟩ ⟨h1, h2, h3, h4⟩
  · have h := congrArg transpose h1
    rwa [transpose_mul, transpose_mul, hQ, ← Matrix.mul_assoc] at h
  · have h := congrArg transpose h2
    rwa [transpose_mul, transpose_mul, hQ, ← Matrix.mul_assoc] at h
  · rw [transpose_mul, transpose_transpose, hQ, ← h4, transpose_mul, hQ]
  · rw [transpose_mul, transpose_transpose, hQ, ← h3, transpose_mul, hQ]

/-- `G G = Q`, `G` being symmetric. -/
private theorem aux_G_mul_G (E : Ellipsoid n) : E.G * E.G = E.Q := by
  have h := E.G_mul_transpose
  rwa [E.G_transpose] at h

/-- `G P G` fixes `G`: `A = G P G G - G` lies in the range of `G` and `G A = Q P Q - Q = 0`, so
`Aᵀ A = 0`. -/
private theorem aux_GPG_mul_G (E : Ellipsoid n) {P : Mat ℝ n n} (hP : IsPinv E.Q P) :
    E.G * P * E.G * E.G = E.G := by -- --- PROOF ---
  set B : Mat ℝ n n := P * E.G * E.G - 1 with hB
  set A : Mat ℝ n n := E.G * B with hA
  have hGA : E.G * A = 0 := by
    rw [hA, ← Matrix.mul_assoc, aux_G_mul_G, hB, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (E.Q * P), aux_G_mul_G, hP.1,
      sub_self]
  have hAA : Aᵀ * A = 0 := by
    rw [hA, transpose_mul, E.G_transpose, Matrix.mul_assoc, hGA, Matrix.mul_zero]
  have hA0 : A = 0 := by
    rw [← conjTranspose_eq_transpose_of_trivial] at hAA
    exact conjTranspose_mul_self_eq_zero.mp hAA
  rw [hA, hB, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hA0
  calc E.G * P * E.G * E.G = E.G * (P * E.G * E.G) := by simp only [Matrix.mul_assoc]
    _ = E.G := hA0


-- =======================================  MAIN THEOREM  ======================================= --

/-- The ellipsoid is `{q + G u | ‖u‖₂ ≤ 1}`, `G = Q^(1/2)`. -/
theorem Ellipsoid.construct_eq_sqrt (E : Ellipsoid n) :
    E.construct = {x | ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧ x = E.q + E.G *ᵥ u} := by -- --- PROOF ---
  set P := E.Qpinv
  have hP : IsPinv E.Q P := E.isPinv_Qpinv
  symm
  have hPt : Pᵀ = P := aux_pinv_transpose (E.psd.isHermitian.eq.trans rfl) hP
  have hGG := aux_G_mul_G E
  have hR := aux_GPG_mul_G E hP
  -- `(G v) ⬝ w = v ⬝ (G w)` and `(P v) ⬝ w = v ⬝ (P w)`, both being symmetric
  have hsym : ∀ (M : Mat ℝ n n), Mᵀ = M → ∀ v w : Vec ℝ n, (M *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (M *ᵥ w) :=
    fun M hM v w => by rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  ext x
  show _ ↔ (x - E.q) ⬝ᵥ P *ᵥ (x - E.q) ≤ 1 ∧ ∃ w, x - E.q = E.Q *ᵥ w
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp only [add_sub_cancel_left]
    refine ⟨?_, P *ᵥ (E.G *ᵥ u), ?_⟩
    · -- `uᵀ G P G u = ‖R u‖₂²`, `R = G P G`, at most `‖u‖₂ ≤ 1`
      have hRt : (E.G * P * E.G)ᵀ = E.G * P * E.G := by
        rw [transpose_mul, transpose_mul, E.G_transpose, hPt, Matrix.mul_assoc]
      have hRR : (E.G * P * E.G) * (E.G * P * E.G) = E.G * P * E.G := by
        calc (E.G * P * E.G) * (E.G * P * E.G) = (E.G * P * E.G * E.G) * P * E.G := by
              simp only [Matrix.mul_assoc]
          _ = E.G * P * E.G := by rw [hR]
      set R := E.G * P * E.G with hRdef
      have hRu : (R *ᵥ u) ⬝ᵥ (R *ᵥ u) = u ⬝ᵥ (R *ᵥ u) := by
        rw [hsym R hRt, mulVec_mulVec, hRR]
      have hq : (E.G *ᵥ u) ⬝ᵥ P *ᵥ (E.G *ᵥ u) = (R *ᵥ u) ⬝ᵥ (R *ᵥ u) := by
        rw [hRu, hsym E.G E.G_transpose, hRdef]
        simp only [mulVec_mulVec, Matrix.mul_assoc]
      have hcs : (R *ᵥ u) ⬝ᵥ (R *ᵥ u) ≤ ‖u‖₂ * ‖R *ᵥ u‖₂ := by
        rw [hRu]
        exact dotProduct_le_norm₂_mul_norm₂ _ _
      rw [hq]
      rw [dotProduct_self] at hcs ⊢
      have h0 := norm₂_nonneg (R *ᵥ u)
      have h1 := mul_le_mul_of_nonneg_right hu h0
      nlinarith
    · -- `G u = G G P G u = Q (P G u)`, `G G P G = (G P G G)ᵀ = G`
      have hL : E.G * (E.G * (P * E.G)) = E.G := by
        have h := congrArg transpose hR
        simpa only [transpose_mul, E.G_transpose, hPt, Matrix.mul_assoc] using h
      rw [← hGG]
      simp only [mulVec_mulVec]
      rw [Matrix.mul_assoc, hL]
  · rintro ⟨hy, w, hw⟩
    -- `u = G P y`, with `G u = Q P Q w = y`
    refine ⟨E.G *ᵥ (P *ᵥ (x - E.q)), ?_, ?_⟩
    · have hsq : ‖E.G *ᵥ (P *ᵥ (x - E.q))‖₂ ^ 2 = (x - E.q) ⬝ᵥ P *ᵥ (x - E.q) := by
        rw [← dotProduct_self, hsym E.G E.G_transpose, mulVec_mulVec, hGG, hsym P hPt,
          mulVec_mulVec, mulVec_mulVec, hP.2.1]
      have h0 := norm₂_nonneg (E.G *ᵥ (P *ᵥ (x - E.q)))
      nlinarith
    · rw [mulVec_mulVec, mulVec_mulVec, hGG, hw, mulVec_mulVec, hP.1, ← hw]
      abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
