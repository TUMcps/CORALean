module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# Any factor of the shape matrix generates the ellipsoid

For any `F` with `F Fᵀ = Q`, of any width `k`, `{q + F u | ‖u‖₂ ≤ 1}` is the ellipsoid of `Q`. The
square root `G` is one such factor; `M G` is one of `M Q Mᵀ`, and two scaled square roots side by
side are one of a weighted sum, which is how an operation computed on `Q` is proved on generators.

Why: a point `F u` lies in the range of `F`, which is that of `F Fᵀ`, so `F u = Q w` and `H v` with
`v = Hᵀ w` is the same point. Its length is that of `Fᵀ w`, as both square to `wᵀ Q w`, and `‖Fᵀ
w‖₂² = (Fᵀ w)ᵀ u ≤ ‖Fᵀ w‖₂ ‖u‖₂` bounds that by `‖u‖₂ ≤ 1`.

## Inputs
* `E` – ellipsoid
* `k` – factor width
* `F` – factor

## Hypotheses
* `hF` – `F Fᵀ = Q`

## Conclusion
* `E` is the image of the unit ball under `F` about `q`
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

/-- `F` and `F Fᵀ` have the same range. -/
private theorem aux_range_mul_transpose {k : ℕ} (F : Mat ℝ n k) :
    LinearMap.range (F * Fᵀ).mulVecLin = LinearMap.range F.mulVecLin := by -- --- PROOF ---
  have hle : LinearMap.range (F * Fᵀ).mulVecLin ≤ LinearMap.range F.mulVecLin := by
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h := Matrix.rank_self_mul_transpose F
  unfold Matrix.rank at h
  exact h

/-- A point of one factor's ball image is a point of the other's. -/
private theorem aux_exists_of_gram_eq {k l : ℕ} (F : Mat ℝ n k) (H : Mat ℝ n l)
    (h : F * Fᵀ = H * Hᵀ) {u : Vec ℝ k} (hu : ‖u‖₂ ≤ 1) :
    ∃ v : Vec ℝ l, ‖v‖₂ ≤ 1 ∧ F *ᵥ u = H *ᵥ v := by -- --- PROOF ---
  -- `F u = F Fᵀ w` for some `w`
  have hmem : F *ᵥ u ∈ LinearMap.range (F * Fᵀ).mulVecLin := by
    rw [aux_range_mul_transpose]
    exact ⟨u, rfl⟩
  obtain ⟨w, hw⟩ := hmem
  simp only [Matrix.mulVecLin_apply] at hw
  set a := Fᵀ *ᵥ w with ha
  -- `‖a‖₂² = aᵀ u`, so `‖a‖₂ ≤ ‖u‖₂`
  have hT : ∀ {m : ℕ} (A : Mat ℝ n m) (x : Vec ℝ m), (Aᵀ *ᵥ w) ⬝ᵥ x = w ⬝ᵥ (A *ᵥ x) := by
    intro m A x
    rw [dotProduct_mulVec, mulVec_transpose]
  have hsq : ‖a‖₂ ^ 2 = a ⬝ᵥ u := by
    rw [← dotProduct_self, ha, hT, mulVec_mulVec, hw, ← hT]
  have hle : ‖a‖₂ ≤ 1 := by
    have hcs := dotProduct_le_norm₂_mul_norm₂ a u
    have h0 := norm₂_nonneg a
    have hu0 := norm₂_nonneg u
    nlinarith
  refine ⟨Hᵀ *ᵥ w, ?_, ?_⟩
  · -- `‖Hᵀ w‖₂² = wᵀ H Hᵀ w = wᵀ F Fᵀ w = ‖a‖₂²`
    have heq : ‖Hᵀ *ᵥ w‖₂ ^ 2 = ‖a‖₂ ^ 2 := by
      rw [← dotProduct_self, ← dotProduct_self, ha, hT, hT, mulVec_mulVec, mulVec_mulVec, h]
    have h1 := norm₂_nonneg (Hᵀ *ᵥ w)
    have h2 := norm₂_nonneg a
    nlinarith
  · rw [mulVec_mulVec, ← h, hw]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Any factor `F` of the shape matrix, `F Fᵀ = Q`, generates the ellipsoid. -/
theorem Ellipsoid.construct_eq_of_factor (E : Ellipsoid n) {k : ℕ} (F : Mat ℝ n k)
    (hF : F * Fᵀ = E.Q) :
    E.construct = {x | ∃ u : Vec ℝ k, ‖u‖₂ ≤ 1 ∧ x = E.q + F *ᵥ u} := by -- --- PROOF ---
  have hG : E.G * E.Gᵀ = F * Fᵀ := by rw [E.G_mul_transpose, hF]
  rw [E.construct_eq_sqrt]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨v, hv, he⟩ := aux_exists_of_gram_eq E.G F hG hu
    exact ⟨v, hv, by rw [he]⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨v, hv, he⟩ := aux_exists_of_gram_eq F E.G hG.symm hu
    exact ⟨v, hv, by rw [he]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
