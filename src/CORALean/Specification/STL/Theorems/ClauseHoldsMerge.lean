module

public import CORALean.Specification.STL.Operations.ClauseMerge
public import CORALean.Specification.STL.Theorems.ClauseHoldsInsert

@[expose] public section

/-!
# The disjunction of two clauses

[1, Lemma 2]: some branch of `cl₁.merge cl₂` holds of `ξ` iff one of `cl₁` or one of `cl₂` does:
`⋁ⱼ(…) ∨ ⋁ⱼ(…)` is one clause.

## Inputs
* `c` – time step
* `cl₁` – first clause
* `cl₂` – second clause
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the merged clause holds iff one of the clauses holds

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

theorem STL.Clause.holds_merge (c : ℝ≥0) (cl₁ cl₂ : STL.Clause X) (ξ : ℝ≥0 → X) :
    (∃ b ∈ STL.Clause.merge cl₁ cl₂, b.Holds c ξ) ↔
      (∃ b ∈ cl₁, b.Holds c ξ) ∨ ∃ b ∈ cl₂, b.Holds c ξ := by -- --- PROOF ---
  induction cl₂ with
  | nil => simp [STL.Clause.merge]
  | cons b rest ih =>
    -- the first branch of `cl₂` goes in last, on top of the merge of the rest
    have : STL.Clause.merge cl₁ (b :: rest) = STL.Clause.insert b (STL.Clause.merge cl₁ rest) :=
      rfl
    rw [this, STL.Clause.holds_insert, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_left_comm


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
