module

public import CORALean.Specification.STL.Operations.BranchMerge
public import CORALean.Specification.STL.Definitions.BranchHolds

@[expose] public section

/-!
# A merged branch holds iff one of the two does

`X_c^j(φ ∨ ϱ) ∨ X_c^j(φ' ∨ ϱ') ≡ X_c^j((φ ∨ φ') ∨ (ϱ ∨ ϱ'))`, for [1, Lemma 2]'s branches at the
same `j`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Branch.holds_merge (c : ℝ≥0) {b b' : STL.Branch X} (hj : b.j = b'.j)
    (ξ : ℝ≥0 → X) : (b.merge b').Holds c ξ ↔ b.Holds c ξ ∨ b'.Holds c ξ := by -- --- PROOF ---
  -- the two branches read the trace at the same times
  unfold STL.Branch.Holds STL.Branch.merge
  simp only [← hj, List.mem_append, Pform.Sat, or_and_right, exists_or]
  constructor
  · rintro (((h | h) | (h | h)) | h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · rintro (((h | h) | h) | ((h | h) | h))
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr h)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
