module

public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalCopies

@[expose] public section

/-!
# A point of `PolyLevelSet.copies`

A point of the copies is a point of `P` in every block of its variables.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the copies is a point of `P` in every block of its variables. -/
theorem PolyLevelSet.mem_copies_iff (P : PolyLevelSet n) (a : ℕ) (x : Vec ℝ (a * n)) :
    x ∈ (P.copies a).construct
      ↔ ∀ j, (fun k => x (finProdFinEquiv (j, k))) ∈ P.construct := by -- --- PROOF ---
  have hop : ∀ j i, (P.copies a).op (finProdFinEquiv (j, i)) = P.op i := fun j i => by
    simp [PolyLevelSet.copies, repVec]
  constructor
  · intro h j i
    have hi := h (finProdFinEquiv (j, i))
    rwa [hop, PolyLevelSet.eval_copies] at hi
  · intro h r
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective r
    rw [hop, PolyLevelSet.eval_copies]
    exact h j i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
