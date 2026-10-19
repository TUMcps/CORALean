module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.And
public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Compact
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Linear
public import CORALean.ContSet.PolyLevelSet.Real.Operations.PadVars
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Relax

/-!
# Polynomial level set operations, collected

CORA's `and_` and `cartProd`, at the stored polynomial data, `padVars`, which adds unread
variables, `relax`, which loosens each row by a variable of its own, `compact`, which merges
repeated monomials, and `linear`, the level set of degree-1 rows. Everything else a level
set offers is reached through `PolyLevelSet.levelSet` (`Conversion/`), which denotes the same set.
-/
