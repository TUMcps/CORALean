module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet
public import CORALean.Global.RepBlockDiag

@[expose] public section

/-!
# `PolyLevelSet.copies` over a floating-point scalar

`a` copies of the rows, each on a fresh block of variables and with its own slack, as over ℝ:
the entries are copied and the off-blocks are `zero`, so nothing rounds and the rows read back as
`Real.PolyLevelSet.copies` (`eval_nominalCore_copies`).

## Inputs
* `P` – polynomial level set
* `a` – number of copies

## Output
* the level set of `a` copies on fresh variables
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a` copies of the rows and of the box, copy `j` on the `j`-th block of variables, each row with
its slack. -/
def PolyLevelSet.copies (P : PolyLevelSet 𝕋 n) (a : ℕ) : PolyLevelSet 𝕋 (a * n) where
  m := a * P.m
  q := a * P.q
  A := repBlockDiag zero a P.A
  R := repBlockDiag 0 a P.R
  b := repVec a P.b
  b_error := repVec a P.b_error
  op := repVec a P.op
  dom := P.dom.repVec a

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
