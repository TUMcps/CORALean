import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplane

/-!
# `projectOnHyperplane` encloses the orthogonal projection

For the unit normal `c`, `(I - c cᵀ) x + d c = x - (c ⬝ x - d) c`, the foot of the perpendicular
from `x` to `{y | c ⬝ y = d}`; `mtimes_outer` and `plus_outer` carry it into the result. Outer only.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Pointwise

variable {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.projectOnHyperplane_outer (s : S n) (c : Vec ℝ n) (d : ℝ) :
    (fun x : Vec ℝ n => x - (c ⬝ᵥ x - d) • c) '' construct s ⊆
      construct (ContSet.projectOnHyperplane s c d) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  refine Plus.plus_outer _ _ ⟨(1 - Matrix.vecMulVec c c).mulVec x, ?_, d • c,
    OfPoint.mem_ofPoint _, ?_⟩
  · refine Mtimes.mtimes_outer (𝕄 := Mat ℝ) _ s ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact ⟨x, hx, rfl⟩
  · funext i
    simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.vecMulVec, Finset.mul_sum,
      sub_smul, mul_comm, mul_left_comm]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
