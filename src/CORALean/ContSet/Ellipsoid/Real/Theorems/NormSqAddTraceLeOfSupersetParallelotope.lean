import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Zonotope.Real.Theorems.SignSumCovariance
import CORALean.Global.EuclideanNorm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The vertices of a parallelotope inside an ellipsoid, summed

For `Z(G, z̄) = {z̄ + Gβ | ‖β‖∞ ≤ 1}` inside `{q + Fu | ‖u‖₂ ≤ 1}`, `F` invertible: each vertex
`z̄ + Gσ` is `q + F(w + Mσ)`, `w = F⁻¹(z̄ - q)`, `M = F⁻¹G`, so `‖w + Mσ‖₂² ≤ 1`; summed over the
`2ⁿ` sign vectors the cross terms cancel and the squares add to `2ⁿ tr(MMᵀ)`
(`Zonotope.sign_sum_covariance`), hence `‖w‖₂² + tr(MMᵀ) ≤ 1`. The bound behind the least volume
in [1, Sec. III-A (Remark a)], and, at equality, behind its uniqueness.

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

theorem Ellipsoid.normSq_add_trace_le_of_superset_parallelotope {G F : Mat ℝ n n}
    (hFu : IsUnit F.det) {z q : Vec ℝ n}
    (hsub : {x | ∃ β : Vec ℝ n, (∀ j, |β j| ≤ 1) ∧ x = z + G *ᵥ β} ⊆
      (⟨n, q, F⟩ : Ellipsoid n).construct) :
    ∑ i, (F⁻¹ *ᵥ (z - q)) i ^ 2 + ((F⁻¹ * G) * (F⁻¹ * G)ᵀ).trace ≤ 1 := by -- --- PROOF ---
  have hvert : ∀ β : Vec ℝ n, (∀ j, |β j| ≤ 1) → ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧
      z + G *ᵥ β = q + F *ᵥ u := fun β hβ => hsub ⟨β, hβ, rfl⟩
  -- `M = F⁻¹G`, `w = F⁻¹(z - q)`: every `w + Mσ` has `‖·‖₂ ≤ 1`
  set M : Mat ℝ n n := F⁻¹ * G with hMdef
  set w : Vec ℝ n := F⁻¹ *ᵥ (z - q) with hwdef
  let σ : (Fin n → Bool) → Vec ℝ n := fun s j => if s j then (1 : ℝ) else -1
  have hball : ∀ s, ∑ i, (w i + (M *ᵥ σ s) i) ^ 2 ≤ 1 := fun s => by
    obtain ⟨u, hu, hzu⟩ := hvert (σ s) fun j => by simp only [σ]; split_ifs <;> simp
    have huw : u = w + M *ᵥ σ s := by
      have hFu' : F *ᵥ u = z - q + G *ᵥ σ s := by
        rw [show F *ᵥ u = (q + F *ᵥ u) - q by abel, ← hzu]; abel
      have hinv : u = F⁻¹ *ᵥ (F *ᵥ u) := by
        rw [mulVec_mulVec, nonsing_inv_mul _ hFu, one_mulVec]
      rw [hinv, hFu', mulVec_add, mulVec_mulVec]
    have h2 := norm₂_sq u
    -- `Σ (wᵢ + (Mσ)ᵢ)² = ‖u‖₂² ≤ 1`
    rw [huw] at h2 hu
    simp only [Pi.add_apply] at h2
    rw [← h2]
    nlinarith [norm₂_nonneg (w + M *ᵥ σ s)]
  -- summed over the `2ⁿ` sign vectors: `2ⁿ(‖w‖² + tr(MMᵀ)) ≤ 2ⁿ`
  obtain ⟨hmean, hcov⟩ := Zonotope.sign_sum_covariance M
  have hcov' : ∀ i, ∑ s : Fin n → Bool, (M *ᵥ σ s) i * (M *ᵥ σ s) i = 2 ^ n * (M * Mᵀ) i i :=
    fun i => hcov i i
  -- expand the square; the mean of `Mσ` is `0`, its second moment `2ⁿ MMᵀ`
  have hsum : ∑ s : Fin n → Bool, ∑ i, (w i + (M *ᵥ σ s) i) ^ 2
      = 2 ^ n * (∑ i, w i ^ 2 + (M * Mᵀ).trace) := by
    rw [Finset.sum_comm]
    have hexp : ∀ i, ∑ s : Fin n → Bool, (w i + (M *ᵥ σ s) i) ^ 2
        = 2 ^ n * w i ^ 2 + 2 * w i * (∑ s : Fin n → Bool, (M *ᵥ σ s) i)
          + ∑ s : Fin n → Bool, (M *ᵥ σ s) i * (M *ᵥ σ s) i := fun i => by
      simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring_nf
    simp only [hexp, hcov']
    -- the cross terms vanish
    have hm : ∀ i, ∑ s : Fin n → Bool, (M *ᵥ σ s) i = 0 := fun i => by
      have := congrFun hmean i
      simpa [Finset.sum_apply] using this
    simp only [hm, mul_zero, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum, trace,
      diag]
    ring
  -- divided by `2ⁿ`
  have hle : ∑ s : Fin n → Bool, ∑ i, (w i + (M *ᵥ σ s) i) ^ 2
      ≤ ∑ _s : Fin n → Bool, (1 : ℝ) := Finset.sum_le_sum fun s _ => hball s
  rw [hsum] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hle
  push_cast at hle
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
