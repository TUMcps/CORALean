module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose
public import CORALean.Global.DmdPinv

@[expose] public section

/-!
# The ellipsoid is CORA's set

CORA's `ellipsoid(Q, q)` documents the set
`{x | (x - q)ᵀ Q⁺ (x - q) ≤ 1, x - q ∈ range Q}`, `Q⁺` the Moore-Penrose pseudo-inverse
(`contains_` and `ellipsoidNorm` test exactly this, through `pinv` on the range of a degenerate
`Q`). That is `construct`, the image of the unit ball under `G = Q^(1/2)`, for every positive
semi-definite `Q`, degenerate ones included; `Theorems/MemOfShapeIff` is the positive definite case,
`Q⁺ = Q⁻¹`. `Q⁺` is any `P` satisfying the four Penrose conditions (`IsPinv`), which determine it.

Why: `P` is symmetric, being the pseudo-inverse of a symmetric matrix, and `R = G P G` fixes the
range of `G` (`R G = G`, as `G (R G - G) = Q P Q - Q = 0` and `R G - G` lies in the range of `G`)
and is symmetric and idempotent. A point `y = G u` is then `Q (P G u)`, in the range of `Q`, and
`yᵀ P y = uᵀ R u = ‖R u‖₂² ≤ ‖u‖₂²`. Conversely `y = Q w` is `G u` for `u = G P y`, of squared
length `yᵀ P Q P y = yᵀ P y`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
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

/-- CORA's ellipsoid: `{x | (x - q)ᵀ Q⁺ (x - q) ≤ 1, x - q ∈ range Q}`. -/
theorem Ellipsoid.construct_eq_pinv (E : Ellipsoid n) {P : Mat ℝ n n} (hP : IsPinv E.Q P) :
    E.construct = {x | (x - E.q) ⬝ᵥ P *ᵥ (x - E.q) ≤ 1 ∧ ∃ w, x - E.q = E.Q *ᵥ w}
    := by -- --- PROOF ---
  have hPt : Pᵀ = P := aux_pinv_transpose (E.psd.isHermitian.eq.trans rfl) hP
  have hGG := aux_G_mul_G E
  have hR := aux_GPG_mul_G E hP
  -- `(G v) ⬝ w = v ⬝ (G w)` and `(P v) ⬝ w = v ⬝ (P w)`, both being symmetric
  have hsym : ∀ (M : Mat ℝ n n), Mᵀ = M → ∀ v w : Vec ℝ n, (M *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (M *ᵥ w) :=
    fun M hM v w => by rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp only [Set.mem_setOf_eq, add_sub_cancel_left]
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
