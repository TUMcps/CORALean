module

public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Operations.Basic

@[expose] public section

/-!
# `mtimes`: the product of two matrices of trees

`mtimes(obj1,obj2)` of `syntaxTree.m`: entry `(i,j)` is `sum(obj1(i,:).*obj2(:,j)')`: the entries
multiplied with `.*` (`times`) and added (`sum`) in the order of the column index. A scalar operand
makes it `times`.

## Inputs
* `m` – rows of the first matrix
* `k` – inner dimension minus one
* `p` – columns of the second matrix
* `A` – first matrix of trees
* `B` – second matrix of trees

## Output
* the matrix product of the trees
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `mtimes(obj1,obj2)`: entry `(i,j)` is `sum(obj1(i,:).*obj2(:,j)')`; the scalar case is `times`.
-/
noncomputable def SyntaxTree.mtimes {m k p : ℕ} (A : Fin m → Fin (k + 1) → SyntaxTree n)
    (B : Fin (k + 1) → Fin p → SyntaxTree n) : Fin m → Fin p → SyntaxTree n :=
  fun i j => sum (times (A i 0) (B 0 j))
    ((List.finRange k).map fun l => times (A i l.succ) (B l.succ j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
