module

public import CORALean.Specification.STL.Operations.ClauseMerge
public import CORALean.Specification.STL.Operations.ClauseInsert
public import CORALean.Specification.STL.Theorems.BranchHoldsMerge

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

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Inserting a branch in a clause. -/
private theorem STL.Clause.aux_holds_insert (c : ℝ≥0) (b : STL.Branch X) (cl : STL.Clause X)
    (ξ : ℝ≥0 → X) : -- --- CONCL ---
    (∃ b' ∈ STL.Clause.insert b cl, b'.Holds c ξ) ↔
      b.Holds c ξ ∨ ∃ b' ∈ cl, b'.Holds c ξ := by -- --- PROOF ---
  induction cl with
  | nil => simp [STL.Clause.insert]
  | cons b' rest ih =>
    by_cases h : b'.j = b.j
    · -- same `j`: the merged branch stands for both
      simp only [STL.Clause.insert, h, if_true, List.mem_cons, exists_eq_or_imp,
        STL.Branch.holds_merge c h]
      rw [or_assoc]
      exact or_left_comm
    · simp only [STL.Clause.insert, h, if_false, List.mem_cons, exists_eq_or_imp, ih]
      exact or_left_comm


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Clause.holds_merge (c : ℝ≥0) (cl₁ cl₂ : STL.Clause X) (ξ : ℝ≥0 → X) : -- --- CONCL ---
    (∃ b ∈ STL.Clause.merge cl₁ cl₂, b.Holds c ξ) ↔
      (∃ b ∈ cl₁, b.Holds c ξ) ∨ ∃ b ∈ cl₂, b.Holds c ξ := by -- --- PROOF ---
  induction cl₂ with
  | nil => simp [STL.Clause.merge]
  | cons b rest ih =>
    -- the first branch of `cl₂` goes in last, on top of the merge of the rest
    have : STL.Clause.merge cl₁ (b :: rest) = STL.Clause.insert b (STL.Clause.merge cl₁ rest) :=
      rfl
    rw [this, STL.Clause.aux_holds_insert, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_left_comm


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
