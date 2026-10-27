module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemOfShapeIff
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

/-!
# An ellipsoid by a factor of the inverse shape matrix

[1, Sec. I (parameterizations)]: an ellipsoid is also `{x | ‖Lᵀ(x − q)‖₂ ≤ 1}` for any factor `L`
of the inverse shape matrix, `L Lᵀ = Q⁻¹`, because `‖Lᵀ w‖₂² = wᵀ L Lᵀ w = wᵀ Q⁻¹ w`: the paper's
`E(q, N)` for the symmetric `N = Q^(-1/2)` (which exists, `N = (Q⁻¹)^(1/2)`) and `E(q, L)`
for the Cholesky factor `L` of `Q⁻¹`, or any other.

## Inputs
* `Q` – shape matrix

## Hypotheses
* `hQ` – `Q` positive definite

## Conclusion
* any factor of `Q⁻¹` gives the norm form of membership

## References

* [1] [A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC),
      2018.](../../../../../../references/2018/halder-cdc-minkowski-sum-ellipsoids.md)
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

/-- [1, Sec. I (parameterizations)]: `‖Lᵀ(x − q)‖₂ ≤ 1` iff `(x − q)ᵀ Q⁻¹ (x − q) ≤ 1`, any `L`. -/
theorem Ellipsoid.mem_iff_norm_factor {Q : Mat ℝ n n} (hQ : Q.PosDef) : -- --- CONCL ---
    (∀ L : Mat ℝ n n, L * Lᵀ = Q⁻¹ → ∀ q x : Vec ℝ n,
      ‖Lᵀ *ᵥ (x - q)‖₂ ≤ 1 ↔ (x - q) ⬝ᵥ Q⁻¹ *ᵥ (x - q) ≤ 1)
    ∧ ∃ N : Mat ℝ n n, Nᵀ = N ∧ N * Nᵀ = Q⁻¹ := by -- --- PROOF ---
  refine ⟨fun L hL q x => ?_, ?_⟩
  · -- `‖Lᵀ w‖₂² = wᵀ L Lᵀ w = wᵀ Q⁻¹ w`
    have hsq : (Lᵀ *ᵥ (x - q)) ⬝ᵥ (Lᵀ *ᵥ (x - q)) = (x - q) ⬝ᵥ Q⁻¹ *ᵥ (x - q) := by
      rw [← hL, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose,
        dotProduct_comm]
    rw [← hsq]
    unfold norm₂
    rw [Real.sqrt_le_iff]
    simp only [dotProduct, sq]
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; exact ⟨zero_le_one, by linarith⟩
  · -- the symmetric square root of `Q⁻¹`
    have hNh : (CFC.sqrt Q⁻¹ : Mat ℝ n n).IsHermitian :=
      (CFC.sqrt_nonneg Q⁻¹).posSemidef.isHermitian
    have hNT : (CFC.sqrt Q⁻¹ : Mat ℝ n n)ᵀ = CFC.sqrt Q⁻¹ := by
      have h := hNh.eq
      simpa [conjTranspose_eq_transpose_of_trivial] using h
    refine ⟨CFC.sqrt Q⁻¹, hNT, ?_⟩
    rw [hNT]
    exact CFC.sqrt_mul_sqrt_self Q⁻¹ hQ.inv.posSemidef.nonneg

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
