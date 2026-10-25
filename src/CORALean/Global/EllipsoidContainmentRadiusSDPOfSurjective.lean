module

public import CORALean.Global.EllipsoidContainmentRadiusSDP
public import CORALean.Global.DmdPinv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# The ellipsoid-in-ellipsoid program with `H⁺ = Hᵀ (H Hᵀ)⁻¹`

[1, Thm. 13] with no pseudo-inverse hypothesis: for `H` onto (`E` non-degenerate),
`H⁺ = Hᵀ (H Hᵀ)⁻¹` satisfies the Penrose conditions (`aux_isPinv_of_surjective`), so
`ellipsoid_containmentRadius_sdp` applies at it, and `Θ = H⁺G`, `θ = H⁺(c - d)` are written
out. `S = [r², ∞)` with `r` Eq. 15 at `p = q = 2`.

## Inputs
* `G` – generator matrix of the inner ellipsoid
* `c` – center of the inner ellipsoid
* `H` – generator matrix of the outer ellipsoid
* `d` – center of the outer ellipsoid

## Hypotheses
* `hH` – the outer generator matrix is onto

## Conclusion
* the squared radius is the program's least feasible value at the explicit pseudo-inverse

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n l : ℕ}

/-- For `H` onto, `H Hᵀ` has a unit determinant. -/
theorem aux_isUnit_det_mul_transpose (H : Mat ℝ n l)
    (hH : Function.Surjective H.mulVec) : -- --- CONCL ---
    IsUnit (H * Hᵀ).det := by -- --- PROOF ---
  rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  intro a b hab
  -- `v = a - b` has `H Hᵀ v = 0`, so `Hᵀ v = 0`, so `v ⟂ Im H = ℝⁿ`
  have hv : (H * Hᵀ) *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  have hHt : Hᵀ *ᵥ (a - b) = 0 := by
    apply dotProduct_self_eq_zero.mp
    rw [mulVec_transpose, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hv,
      dotProduct_zero]
  obtain ⟨β, hβ⟩ := hH (a - b)
  have : (a - b) ⬝ᵥ (a - b) = 0 := by
    conv_rhs => rw [← zero_dotProduct β, ← hHt]
    rw [mulVec_transpose, ← dotProduct_mulVec, hβ]
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp this)


/-- For `H` onto, `Hᵀ (H Hᵀ)⁻¹` is the Moore-Penrose pseudo-inverse of `H`. -/
theorem aux_isPinv_of_surjective (H : Mat ℝ n l) (hH : Function.Surjective
    H.mulVec) : -- --- CONCL ---
    IsPinv H (Hᵀ * (H * Hᵀ)⁻¹) := by -- --- PROOF ---
  have hu := aux_isUnit_det_mul_transpose H hH
  have hone : H * (Hᵀ * (H * Hᵀ)⁻¹) = 1 := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu]
  have hsym : ((H * Hᵀ)⁻¹)ᵀ = (H * Hᵀ)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_mul, transpose_transpose]
  refine ⟨by rw [hone, Matrix.one_mul], ?_, by rw [hone, transpose_one], ?_⟩
  · rw [Matrix.mul_assoc, hone, Matrix.mul_one]
  · rw [transpose_mul, transpose_mul, hsym, transpose_transpose, Matrix.mul_assoc]

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 13] at `H⁺ = Hᵀ (H Hᵀ)⁻¹`: `r(Ê, E)² = min S`, `S = [r², ∞)`. -/
theorem ellipsoid_containmentRadius_sdp_of_surjective (G : Mat ℝ n m) (c : Fin n → ℝ)
    (H : Mat ℝ n l) (d : Fin n → ℝ) (hH : Function.Surjective H.mulVec) :
    let Θ := Hᵀ * (H * Hᵀ)⁻¹ * G
    let θ := (Hᵀ * (H * Hᵀ)⁻¹) *ᵥ (c - d)
    let S := {ρ : ℝ | ∃ δ : ℝ, 0 ≤ δ ∧
      (δ • fromBlocks (1 : Mat ℝ m m) 0 0 (-1 : Mat ℝ 1 1) -
        (fromBlocks (Θᵀ * Θ) (replicateCol (Fin 1) (Θᵀ *ᵥ θ)) (replicateRow (Fin 1) (θ ᵥ* Θ))
          (of fun _ _ => θ ⬝ᵥ θ) - ρ • fromBlocks (0 : Mat ℝ m m) 0 0 (1 : Mat ℝ 1 1))).PosSemidef}
    ∃ ρ, IsLeast S ρ ∧ S = Set.Ici ρ ∧
      (∀ α : Fin m → ℝ, α ⬝ᵥ α ≤ 1 → ∃ β, H *ᵥ β = G *ᵥ α + c - d ∧ √(β ⬝ᵥ β) ≤ √ρ) ∧
      ∃ α : Fin m → ℝ, α ⬝ᵥ α ≤ 1 ∧
        ∀ β, H *ᵥ β = G *ᵥ α + c - d → √ρ ≤ √(β ⬝ᵥ β) :=
  ellipsoid_containmentRadius_sdp G c H d hH _ (aux_isPinv_of_surjective H hH)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
