import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import Mathlib.Data.Matrix.Mul

/-!
# The affine image of an ellipsoid

[1, Sec. II (affine map)]: `A E(q, Q) + b = E(A q + b, A Q Aᵀ)`, for any `A ∈ ℝ^{m×n}`. In the
generator form the image has centre `A q + b` and generator `A G`, whose shape is `A Q Aᵀ`
(`Ellipsoid.shape_mtimes`). A matrix with orthonormal rows and `b = 0` is the projection onto the
subspace those rows span, as the paper adds.

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". In Proc. of the 45th
      IEEE Conference on Decision and Control (CDC), pp. 1498-1503, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.affine_image_exact (A : Mat ℝ m n) (b : Vec ℝ m) (E : Ellipsoid n) :
    (fun x => A *ᵥ x + b) '' E.construct =
      (⟨E.k, A *ᵥ E.q + b, A * E.G⟩ : Ellipsoid m).construct := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    show A *ᵥ (E.q + E.G *ᵥ u) + b = A *ᵥ E.q + b + (A * E.G) *ᵥ u
    rw [Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
    abel
  · rintro ⟨u, hu, rfl⟩
    refine ⟨E.q + E.G *ᵥ u, ⟨u, hu, rfl⟩, ?_⟩
    show A *ᵥ (E.q + E.G *ᵥ u) + b = A *ᵥ E.q + b + (A * E.G) *ᵥ u
    rw [Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
