module

public import CORALean.ContSet.Ellipsoid.Real.Operations.EnclosePointsCov
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqOfFactor

@[expose] public section

/-!
# `enclosePoints` with `'cov'` encloses the points

Outer: every point lies in `Ellipsoid.enclosePointsCov pts T U`, for every orthogonal `T` and `U`
(`T Tᵀ = 1`, `U Uᵀ = 1`) as long as no `ntᵢ` vanishes (for points spanning `ℝⁿ` each rotated
coordinate takes a positive value, since the centered points sum to zero in it). With `u` the
coordinates of the point divided by `ntᵢ · sqrt maxDist`, `‖u‖₂² = Σᵢ (oᵢ / ntᵢ)² / maxDist ≤ 1`
by the definition of `maxDist`. Not exact: the ellipsoid is larger than the hull of the points.

## Inputs
* `pts` – points
* `T` – rotation
* `U` – rotation
* `j` – point index

## Hypotheses
* `hT` – `T` orthogonal
* `hU` – `U` orthogonal
* `hnt` – the scalings are nonzero

## Conclusion
* every point lies in the enclosing ellipsoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.enclosePointsCov_mem [NeZero N] (pts : Fin N → Vec ℝ n) {T U : Mat ℝ n n}
    (hT : T * Tᵀ = 1) (hU : U * Uᵀ = 1)
    (hnt : ∀ i, Ellipsoid.step_enclosePointsNt (Ellipsoid.step_enclosePointsOriented pts T U) i ≠ 0)
    (j : Fin N) : -- --- CONCL ---
    pts j ∈ (Ellipsoid.enclosePointsCov pts T U).construct := by -- --- PROOF ---
  -- the oriented coordinates, the scalings `nt`, the radius `maxDist` and the center
  set O := Ellipsoid.step_enclosePointsOriented pts T U with hO
  set nt := Ellipsoid.step_enclosePointsNt O with hnt'
  set md := Ellipsoid.step_enclosePointsMaxDist O nt with hmd
  set c : Vec ℝ n := (1 / (N : ℝ)) • ∑ j, pts j with hc
  -- the centered point is recovered from its oriented coordinates
  have hback : T *ᵥ (U *ᵥ O j) = pts j - c := by
    have : O j = Uᵀ *ᵥ (Tᵀ *ᵥ (pts j - c)) := rfl
    have e1 : ∀ w : Vec ℝ n, U *ᵥ (Uᵀ *ᵥ w) = w := fun w => by
      rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    have e2 : ∀ w : Vec ℝ n, T *ᵥ (Tᵀ *ᵥ w) = w := fun w => by
      rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
    rw [this, e1, e2]
  -- the squared length of the coefficient vector
  have hle : ∑ i, (O j i / nt i) ^ 2 ≤ md :=
    Finset.le_sup' (fun j => ∑ i, (O j i / nt i) ^ 2) (Finset.mem_univ j)
  -- the coefficients of the point, and that the generators send them back to its coordinates
  set u : Vec ℝ n := fun i => O j i / (nt i * Real.sqrt md) with hu
  have hGu : (Matrix.diagonal fun i => nt i * Real.sqrt md : Mat ℝ n n) *ᵥ u = O j := by
    funext i
    simp only [Matrix.mulVec_diagonal, hu]
    -- either `maxDist = 0` and every coordinate of the point vanishes, or the scaling cancels
    by_cases hs : Real.sqrt md = 0
    · -- `md = 0`: every term of the sum vanishes, so does the point
      have hmd0 : md ≤ 0 := Real.sqrt_eq_zero'.mp hs
      have hz : ∑ i, (O j i / nt i) ^ 2 ≤ 0 := hle.trans hmd0
      have hsq : ∀ i, (O j i / nt i) ^ 2 = 0 := fun i =>
        le_antisymm (le_trans (Finset.single_le_sum (f := fun i => (O j i / nt i) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ i)) hz) (sq_nonneg _)
      have := (pow_eq_zero_iff two_ne_zero).mp (hsq i)
      rw [div_eq_zero_iff] at this
      -- `O j i / nt i = 0` with `nt i ≠ 0` forces `O j i = 0`
      rcases this with h | h
      · simp [hs, h]
      · exact absurd h (hnt i)
    · field_simp [hnt i, hs]
  -- the coefficients lie in the unit ball
  have hmd : 0 ≤ md := le_trans (Finset.sum_nonneg fun i _ => sq_nonneg _) hle
  have hu1 : ‖u‖₂ ≤ 1 := by
    suffices h : u ⬝ᵥ u ≤ 1 by
      rw [dotProduct_self] at h
      exact (pow_le_one_iff_of_nonneg (norm₂_nonneg u) two_ne_zero).mp h
    unfold dotProduct
    by_cases hs : md = 0
    · have hz : ∑ i, (O j i / nt i) ^ 2 ≤ 0 := hs ▸ hle
      have hsq : ∀ i, (O j i / nt i) ^ 2 = 0 := fun i =>
        le_antisymm (le_trans (Finset.single_le_sum (f := fun i => (O j i / nt i) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ i)) hz) (sq_nonneg _)
      -- all coefficients are zero
      have : ∀ i, u i * u i = 0 := fun i => by
        have := (pow_eq_zero_iff two_ne_zero).mp (hsq i)
        rw [div_eq_zero_iff] at this
        simp only [hu, hs, Real.sqrt_zero, mul_zero, div_zero, mul_zero]
      simp [this]
    · -- `md > 0`: each term is `(O j i / nt i)² / md`, summing to at most `1`
      have hpos : 0 < md := lt_of_le_of_ne hmd (Ne.symm hs)
      have hsq : Real.sqrt md ^ 2 = md := Real.sq_sqrt hmd
      have : ∀ i, u i * u i = (O j i / nt i) ^ 2 / md := fun i => by
        simp only [hu]
        conv_rhs => rw [← hsq]
        have := hnt i
        have h2 : Real.sqrt md ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
        field_simp
      simp only [this, ← Finset.sum_div]
      rw [div_le_one hpos]
      exact hle
  -- the point is the center plus the generators applied to the coefficients
  rw [Ellipsoid.construct_eq_of_factor _
    (T * U * (Matrix.diagonal fun i => nt i * Real.sqrt md : Mat ℝ n n)) rfl]
  refine ⟨u, hu1, ?_⟩
  change pts j = c + (T * U * (Matrix.diagonal fun i => nt i * Real.sqrt md : Mat ℝ n n)) *ᵥ u
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGu, hback]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
