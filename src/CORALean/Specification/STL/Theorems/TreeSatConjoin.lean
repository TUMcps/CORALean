module

public import CORALean.Specification.STL.Operations.TreeConjoin

@[expose] public section

/-!
# A conjoined list is satisfied by its members

`res = res & c` over a list, starting from the empty `res = []`: the result is satisfied exactly
when every member is.

## Inputs
* `L` – list of formulas
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the conjunction holds iff every member holds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_conjoin (L : List (STL.Tree n)) (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (STL.Tree.conjoin L).Satisfies ξ ↔ ∀ c ∈ L, c.Satisfies ξ := by -- --- PROOF ---
  suffices ∀ acc : Option (STL.Tree n), ((L.foldl (fun res c => some (res.elim c fun r => .and r c))
      acc).getD .tt).Satisfies ξ ↔ (∀ r ∈ acc, r.Satisfies ξ) ∧ ∀ c ∈ L, c.Satisfies ξ by
    simpa [STL.Tree.conjoin] using this none
  induction L with
  | nil => intro acc; cases acc <;> simp [STL.Tree.Satisfies]
  | cons c L ih =>
    intro acc
    rw [List.foldl_cons, ih]
    cases acc <;> simp [STL.Tree.Satisfies, and_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
