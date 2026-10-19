module

public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

@[expose] public section

/-!
# `PolyLevelSet.linear` over a floating-point scalar

The polynomial level set of degree-1 rows at stored coefficients, each row with its slack:
`|(A x - b)ᵢ| ≤ |b_errorᵢ|` at an equation, its monomials the variables themselves
(`mem_linear_iff`). It reads back as `Real.PolyLevelSet.linear` at the read-back entries.

## Inputs
* `m` – number of rows
* `A` – coefficient matrix
* `b` – right-hand side
* `b_error` – row slack
* `op` – comparison of each row
* `D` – box of the variables

## Output
* the level set of the linear rows
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows `(A x - b)ᵢ ⋈ᵢ 0` with the slacks `b_error` on the box `D`, monomial `k` being `xₖ`. -/
def PolyLevelSet.linear {m : ℕ} (A : Mat 𝕋 m n) (b b_error : Vec 𝕋 m)
    (op : Fin m → Real.CompOp) (D : Interval (Vec 𝕋 n)) : PolyLevelSet 𝕋 n :=
  ⟨m, n, A, Real.PolyZonotope.identE n, b, b_error, op, D⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
