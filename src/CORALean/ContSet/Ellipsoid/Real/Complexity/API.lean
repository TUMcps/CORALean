module

public import CORALean.ContSet.Ellipsoid.Real.Complexity.Time.API

/-!
# Complexity

`Time/` holds the cost of each operation. There is no `Space/`: an ellipsoid's size is its
dimension, fixed by the type, which no operation changes beyond `mtimes`'s `m`.
-/
