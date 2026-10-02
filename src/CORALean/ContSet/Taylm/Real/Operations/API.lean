import CORALean.ContSet.Taylm.Real.Operations.Acos
import CORALean.ContSet.Taylm.Real.Operations.Asin
import CORALean.ContSet.Taylm.Real.Operations.Atan
import CORALean.ContSet.Taylm.Real.Operations.Bounds
import CORALean.ContSet.Taylm.Real.Operations.Compose
import CORALean.ContSet.Taylm.Real.Operations.Const
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import CORALean.ContSet.Taylm.Real.Operations.Cos
import CORALean.ContSet.Taylm.Real.Operations.Cosh
import CORALean.ContSet.Taylm.Real.Operations.Degree
import CORALean.ContSet.Taylm.Real.Operations.Exp
import CORALean.ContSet.Taylm.Real.Operations.Log
import CORALean.ContSet.Taylm.Real.Operations.Mag
import CORALean.ContSet.Taylm.Real.Operations.Minus
import CORALean.ContSet.Taylm.Real.Operations.Mtimes
import CORALean.ContSet.Taylm.Real.Operations.MulTerms
import CORALean.ContSet.Taylm.Real.Operations.Plus
import CORALean.ContSet.Taylm.Real.Operations.PolyBounds
import CORALean.ContSet.Taylm.Real.Operations.Pow
import CORALean.ContSet.Taylm.Real.Operations.Reach
import CORALean.ContSet.Taylm.Real.Operations.Sin
import CORALean.ContSet.Taylm.Real.Operations.Sinh
import CORALean.ContSet.Taylm.Real.Operations.Smul
import CORALean.ContSet.Taylm.Real.Operations.Sqrt
import CORALean.ContSet.Taylm.Real.Operations.Sum
import CORALean.ContSet.Taylm.Real.Operations.Tan
import CORALean.ContSet.Taylm.Real.Operations.Tanh
import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.TermBounds
import CORALean.ContSet.Taylm.Real.Operations.Times
import CORALean.ContSet.Taylm.Real.Operations.Uminus
import CORALean.ContSet.Taylm.Real.Operations.Uplus
import CORALean.ContSet.Taylm.Real.Operations.SupportBound

/-!
# Taylor model operations, collected

CORA's arithmetic on `taylm` (`plus`, `minus`, `uminus`, `uplus`, `times`, `mtimes`, `sum`,
`power`), the range bound `bounds` of `interval`, and the elementary functions `exp`, `log`,
`sqrt`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `tan`, `atan`, `asin`, `acos`, all `taylor` at their
own derivative bound, itself `compose`.
-/
