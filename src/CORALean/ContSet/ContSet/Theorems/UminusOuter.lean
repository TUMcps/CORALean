module

public import CORALean.ContSet.ContSet.Operations.Basic

@[expose] public section

/-!
# `uminus` encloses the negation
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every `-x` with `x` in `S` is in `uminus S`: `mtimes_outer` at `-1`, which reads as
`-1` because `0`, `1` and negation are exact. -/
theorem ContSet.uminus_outer (s : S n) :
    (fun y : Vec ℝ n => -y) '' construct s ⊆
      construct (ContSet.uminus (𝕋 := 𝕋) s) := by -- --- PROOF ---
  rintro _ ⟨y, hy, rfl⟩
  refine Mtimes.mtimes_outer (𝕄 := Mat 𝕋) _ s ?_
  simp only [ContSet.construct_mat, Set.biUnion_singleton, Set.mem_image]
  refine ⟨y, hy, ?_⟩
  have hD : toRealMat (-1 : Mat 𝕋 n n) = -1 := by
    ext i j
    rw [toRealMat_apply, Matrix.neg_apply, Matrix.neg_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [NegScalar.toReal_neg, ExactScalar.toReal_one]
    · rw [NegScalar.toReal_neg, ExactScalar.toReal_zero, neg_zero]
  rw [hD, Matrix.neg_mulVec, Matrix.one_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
