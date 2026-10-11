import CORALean.Global.EllipsoidContainmentRadiusSDP
import CORALean.Global.IsPinvOfSurjective

/-!
# The ellipsoid-in-ellipsoid program with `H⁺ = Hᵀ (H Hᵀ)⁻¹`

[1, Thm. 13] with no pseudo-inverse hypothesis: for `H` onto (`E` non-degenerate),
`H⁺ = Hᵀ (H Hᵀ)⁻¹` satisfies the Penrose conditions (`isPinv_of_surjective`), so
`ellipsoid_containmentRadius_sdp` applies at it, and `Θ = H⁺G`, `θ = H⁺(c - d)` are written
out. `S = [r², ∞)` with `r` Eq. 15 at `p = q = 2`.

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m l : ℕ}


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
  ellipsoid_containmentRadius_sdp G c H d hH _ (isPinv_of_surjective H hH)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
