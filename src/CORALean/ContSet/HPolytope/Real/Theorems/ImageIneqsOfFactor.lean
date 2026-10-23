module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The linear map of an H-polytope, through a singular value decomposition

[1, Eq. 24], general case: with `M = U Σ Vᵀ` and `Σ = [D 0; 0 0] = E S`, `E = [I_r 0; 0 0]`
and `S = diag(D, I)` invertible, `M ⟨A, b⟩ = U E ⟨A V S⁻¹, b⟩` — the remaining map `U E` is the
projection the paper hands to Fourier–Motzkin. The display prints `D ∈ ℝ^{(m-r)×n}`, `Iₙ` for
the identity block of `S` and `U [I_r 0]` for an `m × n` map; the identity holds for any
factorization `M = U E S Vᵀ` with `V` orthogonal and `S` invertible, so `U` and `E` are general.

## Inputs
* `A` – `q × n` matrix
* `b` – offset vector of length `q`
* `M` – `m × n` matrix
* `U` – `m × m` matrix
* `E` – `m × n` matrix
* `S` – `n × n` matrix
* `V` – `n × n` matrix

## Hypotheses
* `hS` – `IsUnit S.det`
* `hV` – `V * Vᵀ = 1`
* `hM` – `M` factors as `U E S Vᵀ`

## Conclusion
* the image under `M = U E S Vᵀ` is the image of `ineqs (A V S⁻¹) b` under `U E`

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.image_ineqs_of_factor (A : Mat ℝ q n) (b : Vec ℝ q) (M : Mat ℝ m n)
    (U : Mat ℝ m m) (E : Mat ℝ m n) (S V : Mat ℝ n n) (hS : IsUnit S.det) (hV : V * Vᵀ = 1)
    (hM : M = U * E * S * Vᵀ) : -- --- CONCL ---
    (M *ᵥ ·) '' (HPolytope.ineqs A b).construct =
      ((U * E) *ᵥ ·) '' (HPolytope.ineqs (A * V * S⁻¹) b).construct := by -- --- PROOF ---
  have hV' : Vᵀ * V = 1 := mul_eq_one_comm.mp hV
  subst hM
  ext y
  constructor
  -- `M x = (U E) (S Vᵀ x)`, and `S Vᵀ x` satisfies the rewritten rows
  · rintro ⟨x, hx, rfl⟩
    refine ⟨S *ᵥ (Vᵀ *ᵥ x), HPolytope.mem_ineqs_iff.mpr fun i => ?_, ?_⟩
    · have hx' := HPolytope.mem_ineqs_iff.mp hx i
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      have : A * V * S⁻¹ * S * Vᵀ = A := by
        rw [Matrix.mul_assoc (A * V), Matrix.nonsing_inv_mul S hS, Matrix.mul_one,
          Matrix.mul_assoc, hV, Matrix.mul_one]
      rw [this]
      exact hx'
    · show (U * E) *ᵥ (S *ᵥ (Vᵀ *ᵥ x)) = (U * E * S * Vᵀ) *ᵥ x
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (U * E)]
  -- back: `w` is `S Vᵀ` of the point `V S⁻¹ w`
  · rintro ⟨w, hw, rfl⟩
    refine ⟨V *ᵥ (S⁻¹ *ᵥ w), HPolytope.mem_ineqs_iff.mpr fun i => ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      exact HPolytope.mem_ineqs_iff.mp hw i
    · show (U * E * S * Vᵀ) *ᵥ (V *ᵥ (S⁻¹ *ᵥ w)) = (U * E) *ᵥ w
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc (U * E * S) Vᵀ V, hV', Matrix.mul_one, Matrix.mul_assoc (U * E) S,
        Matrix.mul_nonsing_inv S hS, Matrix.mul_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
