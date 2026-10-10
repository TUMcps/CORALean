import CORALean.ContSet.Taylm.Real.Operations.GetSyms
import CORALean.ContSet.Taylm.Real.Operations.Mmul
import CORALean.ContSet.Taylm.Real.Operations.Mpower
import CORALean.ContSet.Taylm.Real.Operations.Acos
import CORALean.ContSet.Taylm.Real.Operations.AcosPrinted
import CORALean.ContSet.Taylm.Real.Operations.Antideriv
import CORALean.ContSet.Taylm.Real.Operations.AntiderivPrinted
import CORALean.ContSet.Taylm.Real.Operations.ArcsinShift
import CORALean.ContSet.Taylm.Real.Operations.ArgMaxIdx
import CORALean.ContSet.Taylm.Real.Operations.Asin
import CORALean.ContSet.Taylm.Real.Operations.Atan
import CORALean.ContSet.Taylm.Real.Operations.AtanShift
import CORALean.ContSet.Taylm.Real.Operations.BnbLoop
import CORALean.ContSet.Taylm.Real.Operations.BnbStep
import CORALean.ContSet.Taylm.Real.Operations.Bounds
import CORALean.ContSet.Taylm.Real.Operations.BoxMid
import CORALean.ContSet.Taylm.Real.Operations.BoxRad
import CORALean.ContSet.Taylm.Real.Operations.BranchAndBound
import CORALean.ContSet.Taylm.Real.Operations.CodeEval
import CORALean.ContSet.Taylm.Real.Operations.CodeListMap
import CORALean.ContSet.Taylm.Real.Operations.Compose
import CORALean.ContSet.Taylm.Real.Operations.Const
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import CORALean.ContSet.Taylm.Real.Operations.Cos
import CORALean.ContSet.Taylm.Real.Operations.Cosh
import CORALean.ContSet.Taylm.Real.Operations.CosyGo
import CORALean.ContSet.Taylm.Real.Operations.Empty
import CORALean.ContSet.Taylm.Real.Operations.Degree
import CORALean.ContSet.Taylm.Real.Operations.Exp
import CORALean.ContSet.Taylm.Real.Operations.GlobalMin
import CORALean.ContSet.Taylm.Real.Operations.GoLoop
import CORALean.ContSet.Taylm.Real.Operations.GoLowerBound
import CORALean.ContSet.Taylm.Real.Operations.GoStep
import CORALean.ContSet.Taylm.Real.Operations.HalveBox
import CORALean.ContSet.Taylm.Real.Operations.Hessian
import CORALean.ContSet.Taylm.Real.Operations.HigherTerms
import CORALean.ContSet.Taylm.Real.Operations.IntegrateTerms
import CORALean.ContSet.Taylm.Real.Operations.Intrinsic
import CORALean.ContSet.Taylm.Real.Operations.Inv
import CORALean.ContSet.Taylm.Real.Operations.InvRemS
import CORALean.ContSet.Taylm.Real.Operations.InvSqrt
import CORALean.ContSet.Taylm.Real.Operations.InvTight
import CORALean.ContSet.Taylm.Real.Operations.Ldb
import CORALean.ContSet.Taylm.Real.Operations.LdbLoop
import CORALean.ContSet.Taylm.Real.Operations.LdbStep
import CORALean.ContSet.Taylm.Real.Operations.LinCoef
import CORALean.ContSet.Taylm.Real.Operations.ListMax
import CORALean.ContSet.Taylm.Real.Operations.ListMin
import CORALean.ContSet.Taylm.Real.Operations.Log
import CORALean.ContSet.Taylm.Real.Operations.Mag
import CORALean.ContSet.Taylm.Real.Operations.Minus
import CORALean.ContSet.Taylm.Real.Operations.Mtimes
import CORALean.ContSet.Taylm.Real.Operations.MulTerms
import CORALean.ContSet.Taylm.Real.Operations.OptBnb
import CORALean.ContSet.Taylm.Real.Operations.OptBnbAdv
import CORALean.ContSet.Taylm.Real.Operations.OptLinQuad
import CORALean.ContSet.Taylm.Real.Operations.Plus
import CORALean.ContSet.Taylm.Real.Operations.PolyBounds
import CORALean.ContSet.Taylm.Real.Operations.PolyBoxBounds
import CORALean.ContSet.Taylm.Real.Operations.Pow
import CORALean.ContSet.Taylm.Real.Operations.PowBounds
import CORALean.ContSet.Taylm.Real.Operations.ProdBounds
import CORALean.ContSet.Taylm.Real.Operations.QfbLower
import CORALean.ContSet.Taylm.Real.Operations.QuadForm
import CORALean.ContSet.Taylm.Real.Operations.QuadTerms
import CORALean.ContSet.Taylm.Real.Operations.RangeBound
import CORALean.ContSet.Taylm.Real.Operations.Rdivide
import CORALean.ContSet.Taylm.Real.Operations.Reach
import CORALean.ContSet.Taylm.Real.Operations.ReexpBoxBounds
import CORALean.ContSet.Taylm.Real.Operations.ReexpTerms
import CORALean.ContSet.Taylm.Real.Operations.Reexpand
import CORALean.ContSet.Taylm.Real.Operations.Sin
import CORALean.ContSet.Taylm.Real.Operations.Sinh
import CORALean.ContSet.Taylm.Real.Operations.Smul
import CORALean.ContSet.Taylm.Real.Operations.SplitAt
import CORALean.ContSet.Taylm.Real.Operations.Sqrt
import CORALean.ContSet.Taylm.Real.Operations.Sum
import CORALean.ContSet.Taylm.Real.Operations.Tan
import CORALean.ContSet.Taylm.Real.Operations.Tanh
import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.TermBounds
import CORALean.ContSet.Taylm.Real.Operations.TermBoxBounds
import CORALean.ContSet.Taylm.Real.Operations.Times
import CORALean.ContSet.Taylm.Real.Operations.Uminus
import CORALean.ContSet.Taylm.Real.Operations.Uplus
import CORALean.ContSet.Taylm.Real.Operations.SupportBound
import CORALean.ContSet.Taylm.Real.Operations.Trace
import CORALean.ContSet.Taylm.Real.Operations.Prod
import CORALean.ContSet.Taylm.Real.Operations.Det
import CORALean.ContSet.Taylm.Real.Operations.WidestCoord
import CORALean.ContSet.Taylm.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.Taylm.Real.Operations.RepresentsaPoint
import CORALean.ContSet.Taylm.Real.Operations.BernsteinBasis
import CORALean.ContSet.Taylm.Real.Operations.BernsteinEntry
import CORALean.ContSet.Taylm.Real.Operations.BernsteinDegree
import CORALean.ContSet.Taylm.Real.Operations.BernsteinCoeff
import CORALean.ContSet.Taylm.Real.Operations.OptBernstein
import CORALean.ContSet.Taylm.Real.Operations.QfbSearchStep

/-!
# Taylor model operations, collected

CORA's arithmetic on `taylm` (`plus`, `minus`, `uminus`, `uplus`, `times`, `mtimes`, `sum`,
`power`), the range bound `bounds` of `interval`, and the elementary functions `exp`, `log`,
`sqrt`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `tan`, `atan`, `asin`, `acos`, `inv`, `invSqrt`, all
`taylor` at their own derivative bound, itself `compose`. Beyond CORA: the antiderivative
`antideriv` (and the source's printed `antiderivPrinted`), a code list's run `codeEval` with
`intrinsic`, and range bounding `rangeBound`.
-/
