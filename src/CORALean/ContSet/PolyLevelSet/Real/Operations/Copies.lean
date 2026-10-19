module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.Global.RepBlockDiag

@[expose] public section

/-!
# `PolyLevelSet.copies`

`a` copies of the rows, each on a fresh block of `n` variables: the coefficients and the exponent
matrix sit block-diagonally (`repBlockDiag`) and the right-hand sides and operators repeat
(`repVec`), so copy `j`'s rows read block `j` alone (`mem_copies_iff`). `cartProd` of `a` equal
operands, laid out by `finProdFinEquiv`. Not one of CORA's operations: it is the constraint of
`a` points of a set taken at once, as a convex combination of them needs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a` copies of the rows and of the box, copy `j` on the `j`-th block of variables. -/
def PolyLevelSet.copies (P : PolyLevelSet n) (a : ℕ) : PolyLevelSet (a * n) where
  m := a * P.m
  q := a * P.q
  A := repBlockDiag 0 a P.A
  R := repBlockDiag 0 a P.R
  b := repVec a P.b
  op := repVec a P.op
  dom := P.dom.repVec a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
