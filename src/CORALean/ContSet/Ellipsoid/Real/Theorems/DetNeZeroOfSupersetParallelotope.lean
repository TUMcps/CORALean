import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.Global.EuclideanNorm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# An ellipsoid around a full-dimensional parallelotope has an invertible generator

For invertible `G`, an ellipsoid `{q + Fu | ‖u‖₂ ≤ 1}` with a square generator `F` that contains
`Z(G, z̄) = {z̄ + Gβ | ‖β‖∞ ≤ 1}` has `det F ≠ 0`: a left null vector `v` of `F` makes `vᵀx`
constant on the ellipsoid, so `vᵀ(z̄ ± Geⱼ)` agree and `vᵀG = 0`, `v = 0`. Used for
[1, Sec. III-A (Remark a)], where only such ellipsoids `E(E, e)`, `E ≻ 0`, compete.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.det_ne_zero_of_superset_parallelotope {G F : Mat ℝ n n} (hG : IsUnit G.det)
    {z q : Vec ℝ n} (hsub : {x | ∃ β : Vec ℝ n, (∀ j, |β j| ≤ 1) ∧ x = z + G *ᵥ β} ⊆
      (⟨n, q, F⟩ : Ellipsoid n).construct) : F.det ≠ 0 := by -- --- PROOF ---
  have hvert : ∀ β : Vec ℝ n, (∀ j, |β j| ≤ 1) → ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧
      z + G *ᵥ β = q + F *ᵥ u := fun β hβ => hsub ⟨β, hβ, rfl⟩
  intro hF
  -- a left null vector `v` of `F` would be orthogonal to every `Geⱼ`
  obtain ⟨v, hv0, hvF⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hF
  -- `vᵀ(z ± Geⱼ - q) = vᵀFu = 0` for both signs
  have hvG : v ᵥ* G = 0 := by
    funext j
    have hb : ∀ t : ℝ, |t| ≤ 1 → v ⬝ᵥ (z - q) + t * (v ᵥ* G) j = 0 := fun t ht => by
      obtain ⟨u, -, hu⟩ := hvert (Pi.single j t) fun i => by
        by_cases hij : i = j
        · subst hij; simpa using ht
        · simp [Pi.single_eq_of_ne hij]
      have h := congrArg (v ⬝ᵥ ·) hu
      simp only [dotProduct_add, dotProduct_mulVec, hvF, zero_dotProduct, add_zero,
        dotProduct_single] at h
      rw [dotProduct_sub]
      linear_combination h
    have h1 := hb 1 (by simp)
    have h2 := hb (-1) (by simp)
    simp only [Pi.zero_apply]
    linarith
  apply hv0
  have := congrArg (· ᵥ* G⁻¹) hvG
  simpa [vecMul_vecMul, mul_nonsing_inv _ hG] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
