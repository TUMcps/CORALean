import CORALean.ContSet.ContSet.Operations.Times
import CORALean.Global.ExactScalar

/-!
# `times` encloses the elementwise product
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of `S`, scaled coordinate by coordinate by `v` read as reals, is in
`times v S`: `mtimes_outer` at `diag v`, whose real reading is `diag` of the read vector. -/
theorem ContSet.times_outer (v : Vec 𝕋 n) (s : S n) :
    (fun y : Vec ℝ n => fun i => toReal (v i) * y i) '' construct s ⊆
      construct (ContSet.times v s) := by -- --- PROOF ---
  rintro _ ⟨y, hy, rfl⟩
  refine Mtimes.mtimes_outer (𝕄 := Mat 𝕋) _ s ?_
  simp only [ContSet.construct_mat, Set.biUnion_singleton, Set.mem_image]
  refine ⟨y, hy, ?_⟩
  have hD : toRealMat (Matrix.diagonal v : Mat 𝕋 n n) = Matrix.diagonal (toRealVec v) := by
    ext i j
    rw [toRealMat_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; exact (toRealVec_apply v i).symm
    · exact ExactScalar.toReal_zero
  rw [hD]
  funext i
  rw [Matrix.mulVec_diagonal, toRealVec_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
