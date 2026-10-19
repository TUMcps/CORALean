module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.And
public import CORALean.ContSet.PolyLevelSet.Float.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Float.Operations.PadVars
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Relax
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Compact
public import CORALean.ContSet.PolyLevelSet.Float.Operations.CompactSpec
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Copies
public import CORALean.ContSet.PolyLevelSet.Float.Operations.GetSubset
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Lhs
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Linear
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Switch
public import CORALean.ContSet.PolyLevelSet.Float.Operations.ReindexVars

/-!
# Float polynomial level set operations, collected

`and_`, `cartProd`, `copies`, `padVars`, `reindexVars`, `switch` and `linear`, which copy the
stored rows and slacks or round nothing, `relax`, which moves the slacks into variables of their
own, and `compact` and `getSubset`, whose rounding of the coefficients widens the slacks on the
unit box (`lhs` is the rows' polynomial part `getSubset` works on).
-/
