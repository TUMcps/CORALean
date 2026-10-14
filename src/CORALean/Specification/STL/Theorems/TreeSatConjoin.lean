module

public import CORALean.Specification.STL.Operations.TreeConjoin

@[expose] public section

/-!
# A conjoined list is satisfied by its members

`res = res & c` over a list, starting from the empty `res = []`: the result is satisfied exactly
when every member is.
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

theorem STL.Tree.sat_conjoin (L : List (STL.Tree n)) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.conjoin L).Sat ξ ↔ ∀ c ∈ L, c.Sat ξ := by -- --- PROOF ---
  suffices ∀ acc : Option (STL.Tree n), ((L.foldl (fun res c => some (res.elim c fun r => .and r c))
      acc).getD .tt).Sat ξ ↔ (∀ r ∈ acc, r.Sat ξ) ∧ ∀ c ∈ L, c.Sat ξ by
    simpa [STL.Tree.conjoin] using this none
  induction L with
  | nil => intro acc; cases acc <;> simp [STL.Tree.Sat]
  | cons c L ih =>
    intro acc
    rw [List.foldl_cons, ih]
    cases acc <;> simp [STL.Tree.Sat, and_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
