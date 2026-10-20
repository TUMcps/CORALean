module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# The value of `sum`

`sum(obj)` denotes the sum of its entries.

## Inputs
* `t` – first tree
* `rest` – remaining trees

## Hypotheses
* none

## Conclusion
* the sum node evaluates to the sum of the entries
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} (x : Fin n → ℝ)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `sum` denotes the sum of the entries. -/
theorem SyntaxTree.eval_sum (t : SyntaxTree n) (rest : List (SyntaxTree n)) : -- --- CONCL ---
    (sum t rest).eval x = t.eval x + (rest.map (fun u => u.eval x)).sum := by -- --- PROOF ---
  induction rest generalizing t with
  | nil => simp [sum]
  | cons u us ih =>
    have := ih (t.plus u)
    simp only [sum, List.foldl_cons] at this ⊢
    rw [this]
    simp [eval, SyntaxTree.plus, Binary.fn, add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
