module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

@[expose] public section

/-!
# `PolyLevelSet.linear`

The polynomial level set of degree-1 rows: `(A x - b)ᵢ ⋈ᵢ 0`, its monomials the variables
themselves (`PolyZonotope.identE`), so a point is in it when it meets `A x - b` row by row
(`mem_linear_iff`). A linear system of inequalities, strict ones and equations, written as the
polynomial data every other operation computes with.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows `(A x - b)ᵢ ⋈ᵢ 0`, monomial `k` being `xₖ`. -/
def PolyLevelSet.linear {m : ℕ} (A : Mat ℝ m n) (b : Vec ℝ m) (op : Fin m → CompOp) :
    PolyLevelSet n :=
  ⟨m, n, A, PolyZonotope.identE n, b, op⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
