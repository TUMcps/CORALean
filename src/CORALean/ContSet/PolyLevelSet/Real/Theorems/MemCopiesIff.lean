module

public import CORALean.ContSet.Interval.Real.Theorems.MemRepVecIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalCopies

@[expose] public section

/-!
# A point of `PolyLevelSet.copies`

A point of the copies is a point of `P` in every block of its variables.

## Inputs
* `P` – polynomial level set
* `a` – number of copies
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` lies in the copies iff each block of variables lies in `P`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the copies is a point of `P`, box and rows, in every block of its variables. -/
theorem PolyLevelSet.mem_copies_iff (P : PolyLevelSet n) (a : ℕ)
    (x : Vec ℝ (a * n)) : -- --- CONCL ---
    x ∈ (P.copies a).construct
      ↔ ∀ j, (fun k => x (finProdFinEquiv (j, k))) ∈ P.construct := by -- --- PROOF ---
  have hop : ∀ j i, (P.copies a).op (finProdFinEquiv (j, i)) = P.op i := fun j i => by
    simp [PolyLevelSet.copies, repVec]
  have hdom := Interval.mem_repVec_iff a P.dom x
  constructor
  · intro h j
    refine ⟨(hdom.mp h.1) j, fun i => ?_⟩
    have hi := h.2 (finProdFinEquiv (j, i))
    rwa [hop, PolyLevelSet.eval_copies] at hi
  · intro h
    refine ⟨hdom.mpr fun j => (h j).1, fun r => ?_⟩
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective r
    rw [hop, PolyLevelSet.eval_copies]
    exact (h j).2 i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
