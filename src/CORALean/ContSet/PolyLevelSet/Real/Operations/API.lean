module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.And
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Compact
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Linear
public import CORALean.ContSet.PolyLevelSet.Real.Operations.PadVars
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Relax
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Copies
public import CORALean.ContSet.PolyLevelSet.Real.Operations.GetSubset
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Lhs
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Switch
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Eliminate
public import CORALean.ContSet.PolyLevelSet.Real.Operations.ReindexVars

/-!
# Polynomial level set operations, collected

CORA's `and_` and `cartProd`, at the stored polynomial data, `andRows`, `and_`'s rows on the first
operand's box, `padVars`, which adds unread variables, `reindexVars`, which reads the rows at other
variables, `copies`, which repeats the rows on fresh blocks of variables, `relax`, which loosens
each row by a variable of its own, `switch`, which weights each right-hand side by a monomial,
`compact`, which merges repeated monomials, `getSubset`, which re-parametrizes a variable (on the
rows' polynomial part `lhs`), `eliminate`, which solves a row for a monomial and substitutes it,
and `linear`, the level set of degree-1 rows, each on its box. Everything else a level set offers
is reached through `PolyLevelSet.levelSet` (`Conversion/`), which denotes the same set.
-/
