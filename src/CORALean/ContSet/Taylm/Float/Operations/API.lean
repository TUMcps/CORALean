import CORALean.ContSet.Taylm.Float.Operations.BelowPow
import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Taylm.Float.Operations.CodeEval
import CORALean.ContSet.Taylm.Float.Operations.Compose
import CORALean.ContSet.Taylm.Float.Operations.Const
import CORALean.ContSet.Taylm.Float.Operations.Empty
import CORALean.ContSet.Taylm.Float.Operations.ConstCoef
import CORALean.ContSet.Taylm.Float.Operations.Exp
import CORALean.ContSet.Taylm.Float.Operations.Intrinsic
import CORALean.ContSet.Taylm.Float.Operations.Log
import CORALean.ContSet.Taylm.Float.Operations.Hyperbolic
import CORALean.ContSet.Taylm.Float.Operations.RangeBound
import CORALean.ContSet.Taylm.Float.Operations.Sinh
import CORALean.ContSet.Taylm.Float.Operations.Cosh
import CORALean.ContSet.Taylm.Float.Operations.LogCoef
import CORALean.ContSet.Taylm.Float.Operations.TrigCoef
import CORALean.ContSet.Taylm.Float.Operations.UnitRemainder
import CORALean.ContSet.Taylm.Float.Operations.Sin
import CORALean.ContSet.Taylm.Float.Operations.Cos
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
import CORALean.ContSet.Taylm.Float.Operations.Uplus
import CORALean.ContSet.Taylm.Float.Operations.BoundDot
import CORALean.ContSet.Taylm.Float.Operations.Tan
import CORALean.ContSet.Taylm.Float.Operations.Tanh
import CORALean.ContSet.Taylm.Float.Operations.Trace
import CORALean.ContSet.Taylm.Float.Operations.Prod
import CORALean.ContSet.Taylm.Float.Operations.Det
import CORALean.ContSet.Taylm.Float.Operations.Taylor
import CORALean.ContSet.Taylm.Float.Operations.MagUp
import CORALean.ContSet.Taylm.Float.Operations.Atan
import CORALean.ContSet.Taylm.Float.Operations.ArcsinCoef
import CORALean.ContSet.Taylm.Float.Operations.ArcsinBound
import CORALean.ContSet.Taylm.Float.Operations.Asin
import CORALean.ContSet.Taylm.Float.Operations.Acos
import CORALean.ContSet.Taylm.Float.Operations.SqrtCoef
import CORALean.ContSet.Taylm.Float.Operations.SqrtBound
import CORALean.ContSet.Taylm.Float.Operations.Sqrt

/-!
# Float Taylor model operations, collected

The exact layer's arithmetic with each coefficient computation enclosed and its width added
to the remainder, and `exp` and `log` with every constant of their expansions enclosed.
`codeEval` runs a code list with them, and `rangeBound` bounds its range over a box.
-/
