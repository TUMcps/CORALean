module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `mtimes` over floats: the product of two matrices of trees

`mtimes(obj1,obj2)` of `syntaxTree.m` over float trees: entry `(i,j)` is
`sum(obj1(i,:).*obj2(:,j)')`, the entries multiplied (`timesFloat`) and added (`sumFloat`) in the
order of the column index, as `mtimes` does. Every entry is sound when the entries are
(`isSound_mtimesFloat`).

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
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `mtimes(obj1,obj2)`: entry `(i,j)` is `sum(obj1(i,:).*obj2(:,j)')`. -/
def SyntaxTree.mtimesFloat {m k p : ℕ} (A : Fin m → Fin (k + 1) → Float.SyntaxTree 𝕋 n)
    (B : Fin (k + 1) → Fin p → Float.SyntaxTree 𝕋 n) : Fin m → Fin p → Float.SyntaxTree 𝕋 n :=
  fun i j => SyntaxTree.sumFloat (SyntaxTree.timesFloat (A i 0) (B 0 j))
    ((List.finRange k).map fun l => SyntaxTree.timesFloat (A i l.succ) (B l.succ j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
