module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The linear map of an H-polytope by an invertible matrix

[1, Eq. 24], first case: `M ⟨A, b⟩ = ⟨A M⁻¹, b⟩` for square invertible `M`, since `y = M x`
exactly when `x = M⁻¹ y`.

## Inputs
* `A` – `q × n` matrix
* `b` – offset vector of length `q`
* `M` – `n × n` matrix

## Hypotheses
* `hM` – `IsUnit M.det`

## Conclusion
* the image under an invertible `M` is `ineqs (A M⁻¹) b`

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

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.image_ineqs_of_invertible (A : Mat ℝ q n) (b : Vec ℝ q) (M : Mat ℝ n n)
    (hM : IsUnit M.det) : -- --- CONCL ---
    (M *ᵥ ·) '' (HPolytope.ineqs A b).construct = (HPolytope.ineqs (A * M⁻¹)
    b).construct := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine HPolytope.mem_ineqs_iff.mpr fun i => ?_
    show ((A * M⁻¹) *ᵥ (M *ᵥ x)) i ≤ b i
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM, Matrix.mul_one]
    exact HPolytope.mem_ineqs_iff.mp hx i
  · intro hy
    refine ⟨M⁻¹ *ᵥ y, HPolytope.mem_ineqs_iff.mpr ?_, ?_⟩
    · intro i
      rw [Matrix.mulVec_mulVec]
      exact HPolytope.mem_ineqs_iff.mp hy i
    · show M *ᵥ (M⁻¹ *ᵥ y) = y
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
