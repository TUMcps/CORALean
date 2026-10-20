module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# The value of `prod`

`prod(obj)` denotes the product of its entries.

## Inputs
* `t` – first tree
* `rest` – remaining trees

## Hypotheses
* none

## Conclusion
* the product node evaluates to the product of the entries
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} (x : Fin n → ℝ)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `prod` denotes the product of the entries. -/
theorem SyntaxTree.eval_prod (t : SyntaxTree n) (rest : List (SyntaxTree n)) :
    (prod t rest).eval x = t.eval x * (rest.map (fun u => u.eval x)).prod := by -- --- PROOF ---
  induction rest generalizing t with
  | nil => simp [prod]
  | cons u us ih =>
    have := ih (t.times u)
    simp only [prod, List.foldl_cons] at this ⊢
    rw [this]
    simp [eval, SyntaxTree.times, Binary.fn, mul_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
