module

public import CORALean.ContSet.LevelSet.Float.Operations.API
public import CORALean.ContSet.LevelSet.Float.Theorems.API

/-!
# Level sets at float bounds, collected

No float representation: the level set keeps its real function, which nothing evaluates. What
runs at float are the sign tests on bounds of that function's range, which CORA computes by
interval evaluation and which are stored floats here: `Operations` holds the tests, `Theorems`
what a certain answer proves.
-/
