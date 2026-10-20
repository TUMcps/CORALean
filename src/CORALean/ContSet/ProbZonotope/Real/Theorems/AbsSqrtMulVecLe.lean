module

public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope

@[expose] public section

/-!
# A coordinate of the covariance's square root applied to a cube

For a positive semidefinite `Σ` with symmetric square root `g`, a coefficient vector `β` in the unit
cube moves coordinate `k` of `g β` by at most `√(n Σₖₖ)`: by Cauchy-Schwarz the product is at most
`√(Σⱼ gₖⱼ²) √(Σⱼ βⱼ²)`, and `Σⱼ gₖⱼ² = (g gᵀ)ₖₖ = Σₖₖ`, `Σⱼ βⱼ² ≤ n`. This bounds the
confidence set `zonotope(probZ, m)` by a box that reads the covariance's diagonal alone, which is
what a float implementation can compute without a matrix square root.

## Inputs
* `S` – `n × n` matrix
* `γ` – vector of length `n`
* `k` – index below `n`

## Hypotheses
* `hS` – `S.PosSemidef`
* `hγ` – `∀ j, |γ j| ≤ 1`

## Conclusion
* each coordinate of `√S γ` is at most `√(n S k k)` in absolute value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.abs_sqrt_mulVec_le {S : Mat ℝ n n} (hS : S.PosSemidef) {γ : Vec ℝ n}
    (hγ : ∀ j, |γ j| ≤ 1) (k : Fin n) : -- --- CONCL ---
    |(CFC.sqrt S *ᵥ γ) k| ≤ Real.sqrt (n * S k k) := by -- --- PROOF ---
  set B := CFC.sqrt S
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hBt : Bᵀ = B := by
    have := (CFC.sqrt_nonneg S).isSelfAdjoint
    simpa [IsSelfAdjoint, star_eq_conjTranspose] using this
  -- the squares of a row of `B` sum to the diagonal entry of `S`
  have hrow : ∑ j, B k j ^ 2 = S k k := by
    rw [← hBB, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : B j k = B k j := congrFun (congrFun hBt k) j
    rw [this, sq]
  -- the squares of the coefficients sum to at most `n`
  have hcube : ∑ j, γ j ^ 2 ≤ n := by
    calc ∑ j, γ j ^ 2 ≤ ∑ _j : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by
            rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hγ j)
      _ = n := by simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B k j) γ
  refine Real.abs_le_sqrt ?_
  calc (B *ᵥ γ) k ^ 2 = (∑ j, B k j * γ j) ^ 2 := rfl
    _ ≤ (∑ j, B k j ^ 2) * ∑ j, γ j ^ 2 := hcs
    _ ≤ S k k * n := by
        rw [hrow]
        exact mul_le_mul_of_nonneg_left hcube (hS.diag_nonneg)
    _ = n * S k k := mul_comm _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
