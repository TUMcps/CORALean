module

public import CORALean.ContSet.ContSet.Operations.Project

@[expose] public section

/-!
# `ContSet.project` encloses the projection

Every point of the set, read at `dims`, lies in `project s dims`: it is the selection matrix
applied to the point, which `mtimes_outer` covers. Outer, and for any `dims`, repeated or not.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.project_outer (s : S n) (dims : Fin k → Fin n) :
    (fun x : Vec ℝ n => (fun i => x (dims i) : Vec ℝ k)) '' construct s ⊆
      construct (ContSet.project (𝕋 := 𝕋) s dims) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  refine Mtimes.mtimes_outer (𝕄 := Mat 𝕋) _ s ?_
  simp only [ContSet.construct_mat, Set.biUnion_singleton, Set.mem_image]
  refine ⟨x, hx, ?_⟩
  funext i
  -- the selection matrix reads back as the real indicator matrix
  have hE : ∀ j, toRealMat (Matrix.of fun i j => if dims i = j then (1 : 𝕋) else 0 : Mat 𝕋 k n)
      i j = if dims i = j then 1 else 0 := by
    intro j
    rw [toRealMat_apply]
    simp only [Matrix.of_apply]
    split_ifs
    · exact ExactScalar.toReal_one
    · exact ExactScalar.toReal_zero
  simp [Matrix.mulVec, dotProduct, hE]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
