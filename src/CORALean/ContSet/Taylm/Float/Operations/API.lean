import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Taylm.Float.Operations.Compose
import CORALean.ContSet.Taylm.Float.Operations.Const
import CORALean.ContSet.Taylm.Float.Operations.ConstCoef
import CORALean.ContSet.Taylm.Float.Operations.Exp
import CORALean.ContSet.Taylm.Float.Operations.Log
import CORALean.ContSet.Taylm.Float.Operations.LogCoef
import CORALean.ContSet.Taylm.Float.Operations.Minus
import CORALean.ContSet.Taylm.Float.Operations.Mtimes
import CORALean.ContSet.Taylm.Float.Operations.Plus
import CORALean.ContSet.Taylm.Float.Operations.PolyBounds
import CORALean.ContSet.Taylm.Float.Operations.Pow
import CORALean.ContSet.Taylm.Float.Operations.Smul
import CORALean.ContSet.Taylm.Float.Operations.Sum
import CORALean.ContSet.Taylm.Float.Operations.TermBounds
import CORALean.ContSet.Taylm.Float.Operations.Times
import CORALean.ContSet.Taylm.Float.Operations.Uminus
import CORALean.ContSet.Taylm.Float.Operations.BoundDot

/-!
# Float Taylor model operations, collected

The exact layer's arithmetic with each coefficient computation enclosed and its width added
to the remainder, and `exp` and `log` with every constant of their expansions enclosed.
-/
