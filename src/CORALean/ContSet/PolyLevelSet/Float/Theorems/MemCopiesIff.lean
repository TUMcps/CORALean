module

public import CORALean.ContSet.PolyLevelSet.Float.Theorems.EvalNominalCoreCopies
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalCopies

@[expose] public section

/-!
# A point of `PolyLevelSet.copies`, over a floating-point scalar

A point of the copies meets `P`'s rows, each within its slack, in every block of its variables.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the copies is a point of `P` in every block of its variables. -/
theorem PolyLevelSet.mem_copies_iff (P : PolyLevelSet 𝕋 n) (a : ℕ) (x : Vec ℝ (a * n)) :
    x ∈ (P.copies a).construct
      ↔ ∀ j, (fun k => x (finProdFinEquiv (j, k))) ∈ P.construct := by -- --- PROOF ---
  have hrow : ∀ j i, ((P.copies a).op (finProdFinEquiv (j, i))).IsMetWithin
      ((P.copies a).nominalCore.eval x (finProdFinEquiv (j, i)))
      |toReal ((P.copies a).b_error (finProdFinEquiv (j, i)))|
      ↔ (P.op i).IsMetWithin (P.nominalCore.eval (fun k => x (finProdFinEquiv (j, k))) i)
        |toReal (P.b_error i)| := fun j i => by
    rw [PolyLevelSet.eval_nominalCore_copies, Real.PolyLevelSet.eval_copies]
    simp only [PolyLevelSet.copies, repVec, Equiv.symm_apply_apply]
  constructor
  · intro h j i
    exact (hrow j i).mp (h _)
  · intro h r
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective r
    exact (hrow j i).mpr (h j i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
