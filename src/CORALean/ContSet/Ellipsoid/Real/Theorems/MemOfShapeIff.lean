module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfShapeEq

@[expose] public section

/-!
# The points of an ellipsoid of given shape

For positive-definite `Q`, `x` is in `Ellipsoid.ofShape Q q` iff `(x − q)ᵀ Q⁻¹ (x − q) ≤ 1`:
the two descriptions of an ellipsoid, as the affine image of the unit ball under `N = Q^(1/2)`
and as a sublevel set of the quadratic form of `Q⁻¹` ([1, Eq. 5], [2, Sec. 1.1 (ellipse)]).
With `x − q = N u`, `(N u)ᵀ Q⁻¹ (N u) = uᵀ u`, since `Q⁻¹ = N⁻¹ N⁻¹`.

## Inputs
* `Q` – shape matrix
* `q` – center
* `x` – point

## Hypotheses
* `hQ` – `Q` positive definite

## Conclusion
* `x ∈ E(Q, q)` iff `(x − q)ᵀ Q⁻¹ (x − q) ≤ 1`

## References

* [1] [A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC),
      2018.](../../../../../../references/2018/halder-cdc-minkowski-sum-ellipsoids.md)
* [2] [M. Černý. "Goffin's algorithm for zonotopes". Kybernetika,
      2012.](../../../../../../references/2012/cerny-kybernetika-goffin-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [2, Sec. 1.1 (ellipse)]: `x ∈ E(Q, q)` iff `(x − q)ᵀ Q⁻¹ (x − q) ≤ 1`. -/
theorem Ellipsoid.mem_ofShape_iff {Q : Mat ℝ n n} (hQ : Q.PosDef) (q x : Vec ℝ n) : -- --- CONCL ---
    x ∈ (Ellipsoid.ofShape Q q).construct ↔ (x - q) ⬝ᵥ Q⁻¹ *ᵥ (x - q) ≤ 1 := by -- --- PROOF ---
  -- the ellipsoid as `q + G u`, `‖u‖₂ ≤ 1`
  simp only [Ellipsoid.construct_eq_sqrt] at *
  rw [Ellipsoid.ofShape_eq hQ.posSemidef]
  set N : Mat ℝ n n := CFC.sqrt Q with hN
  have hNh : N.IsHermitian := (CFC.sqrt_nonneg Q).posSemidef.isHermitian
  have hNT : Nᵀ = N := by
    have h := hNh.eq
    simpa [conjTranspose_eq_transpose_of_trivial] using h
  have hNN : N * N = Q := CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg
  -- `N` is invertible, with `Q⁻¹ = N⁻¹ N⁻¹`
  have hQu : IsUnit Q.det := (isUnit_iff_isUnit_det Q).1 hQ.isUnit
  have hNu : IsUnit N.det := by
    have : IsUnit (N * N).det := hNN ▸ hQu
    rw [det_mul] at this
    exact (IsUnit.mul_iff.1 this).1
  have hNi : N * N⁻¹ = 1 := mul_nonsing_inv N hNu
  have hNi' : N⁻¹ * N = 1 := nonsing_inv_mul N hNu
  have hQi : Q⁻¹ = N⁻¹ * N⁻¹ := by
    rw [← hNN, Matrix.mul_inv_rev]
  have hNiT : (N⁻¹)ᵀ = N⁻¹ := by rw [transpose_nonsing_inv, hNT]
  -- the quadratic form of `Q⁻¹` at `N u` is `uᵀ u`
  have hq : ∀ u : Vec ℝ n, (N *ᵥ u) ⬝ᵥ Q⁻¹ *ᵥ (N *ᵥ u) = u ⬝ᵥ u := by
    intro u
    have h1 : N⁻¹ * N⁻¹ * N = N⁻¹ := by rw [Matrix.mul_assoc, hNi', Matrix.mul_one]
    rw [mulVec_mulVec, hQi, h1, dotProduct_mulVec, ← mulVec_transpose, hNiT, mulVec_mulVec, hNi',
      one_mulVec]
  -- the Euclidean ball is the sublevel set of `uᵀ u`
  have hnorm : ∀ u : Vec ℝ n, ‖u‖₂ ≤ 1 ↔ u ⬝ᵥ u ≤ 1 := by
    intro u
    unfold norm₂
    rw [Real.sqrt_le_iff]
    simp only [dotProduct, sq]
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; exact ⟨zero_le_one, by linarith⟩
  constructor
  · -- a point `q + N u` of the ball image has form `uᵀ u ≤ 1`
    rintro ⟨u, hu, rfl⟩
    show (q + N *ᵥ u - q) ⬝ᵥ Q⁻¹ *ᵥ (q + N *ᵥ u - q) ≤ 1
    rw [add_sub_cancel_left, hq]
    exact (hnorm u).1 hu
  · -- conversely `u = N⁻¹ (x − q)` is in the ball and maps to `x`
    intro h
    obtain ⟨u, hu⟩ : ∃ u : Vec ℝ n, u = N⁻¹ *ᵥ (x - q) := ⟨_, rfl⟩
    refine ⟨u, (hnorm _).2 ?_, ?_⟩
    all_goals subst hu
    · have := hq (N⁻¹ *ᵥ (x - q))
      rw [mulVec_mulVec, hNi, one_mulVec] at this
      rw [← this]
      exact h
    · show x = q + N *ᵥ (N⁻¹ *ᵥ (x - q))
      rw [mulVec_mulVec, hNi, one_mulVec]
      abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
