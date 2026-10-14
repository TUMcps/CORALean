module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.Mtimes
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.EvalSum

@[expose] public section

/-!
# The value of `mtimes`

Entry `(i,j)` of `mtimes(obj1,obj2)` denotes the sum of the products `obj1(i,l) obj2(l,j)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} (x : Fin n → ℝ)


-- =======================================  MAIN THEOREM  ======================================= --

/-- Entry `(i,j)` of `mtimes` denotes the matrix product. -/
theorem SyntaxTree.eval_mtimes {m k p : ℕ} (A : Fin m → Fin (k + 1) → SyntaxTree n)
    (B : Fin (k + 1) → Fin p → SyntaxTree n) (i : Fin m) (j : Fin p) :
    (mtimes A B i j).eval x = ∑ l, (A i l).eval x * (B l j).eval x := by -- --- PROOF ---
  rw [Fin.sum_univ_succ]
  simp only [mtimes, eval_sum, SyntaxTree.times, eval, Binary.fn]
  congr 1
  rw [List.map_map, Fin.sum_univ_def]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
