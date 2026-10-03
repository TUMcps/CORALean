import CORALean.ContSet.Taylm.Real.Operations.Sum
import CORALean.ContSet.Taylm.Real.Operations.Smul
import CORALean.ContSet.Taylm.Real.Operations.Times

/-!
# `Taylm.det`

CORA's `det` of a square matrix of models, by expansion along the first row: a `1 × 1` matrix is
its entry, else `Σⱼ (-1)^(j+1) · obj(1,j) · det(A₁)` with `A₁` the matrix without row `1` and
column `j`; the sign scales the entry (`smul`) and the product with the minor's determinant is
`times`. The sum is `Taylm.sum`, ending in the zero model where CORA starts from the number `0`.
The matrix is at least `1 × 1`, as CORA's recursion stops there.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.det : {d : ℕ} → (Fin (d + 1) → Fin (d + 1) → Taylm n) → Taylm n
  | 0, A => A 0 0
  | _ + 1, A =>
    Taylm.sum fun j =>
      ((A 0 j).smul ((-1) ^ (j : ℕ))).times (Taylm.det fun i k => A i.succ (j.succAbove k))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
