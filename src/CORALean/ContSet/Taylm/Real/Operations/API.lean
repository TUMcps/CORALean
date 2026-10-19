module

public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Mmul
public import CORALean.ContSet.Taylm.Real.Operations.Mpower
public import CORALean.ContSet.Taylm.Real.Operations.Acos
public import CORALean.ContSet.Taylm.Real.Operations.AcosPrinted
public import CORALean.ContSet.Taylm.Real.Operations.Antideriv
public import CORALean.ContSet.Taylm.Real.Operations.AntiderivPrinted
public import CORALean.ContSet.Taylm.Real.Operations.ArcsinShift
public import CORALean.ContSet.Taylm.Real.Operations.ArgMaxIdx
public import CORALean.ContSet.Taylm.Real.Operations.Asin
public import CORALean.ContSet.Taylm.Real.Operations.Atan
public import CORALean.ContSet.Taylm.Real.Operations.AtanShift
public import CORALean.ContSet.Taylm.Real.Operations.BnbLoop
public import CORALean.ContSet.Taylm.Real.Operations.BnbStep
public import CORALean.ContSet.Taylm.Real.Operations.Bounds
public import CORALean.ContSet.Taylm.Real.Operations.BranchAndBound
public import CORALean.ContSet.Taylm.Real.Operations.CodeEval
public import CORALean.ContSet.Taylm.Real.Operations.CodeListMap
public import CORALean.ContSet.Taylm.Real.Operations.Compose
public import CORALean.ContSet.Taylm.Real.Operations.Cos
public import CORALean.ContSet.Taylm.Real.Operations.Cosh
public import CORALean.ContSet.Taylm.Real.Operations.CosyGo
public import CORALean.ContSet.Taylm.Real.Operations.Exp
public import CORALean.ContSet.Taylm.Real.Operations.GlobalMin
public import CORALean.ContSet.Taylm.Real.Operations.GoLowerBound
public import CORALean.ContSet.Taylm.Real.Operations.HalveBox
public import CORALean.ContSet.Taylm.Real.Operations.Hessian
public import CORALean.ContSet.Taylm.Real.Operations.HigherTerms
public import CORALean.ContSet.Taylm.Real.Operations.IntegrateTerms
public import CORALean.ContSet.Taylm.Real.Operations.Intrinsic
public import CORALean.ContSet.Taylm.Real.Operations.Inv
public import CORALean.ContSet.Taylm.Real.Operations.InvRemS
public import CORALean.ContSet.Taylm.Real.Operations.InvSqrt
public import CORALean.ContSet.Taylm.Real.Operations.InvTight
public import CORALean.ContSet.Taylm.Real.Operations.Ldb
public import CORALean.ContSet.Taylm.Real.Operations.LdbLoop
public import CORALean.ContSet.Taylm.Real.Operations.LdbStep
public import CORALean.ContSet.Taylm.Real.Operations.LinCoef
public import CORALean.ContSet.Taylm.Real.Operations.ListMax
public import CORALean.ContSet.Taylm.Real.Operations.ListMin
public import CORALean.ContSet.Taylm.Real.Operations.Log
public import CORALean.ContSet.Taylm.Real.Operations.Mag
public import CORALean.ContSet.Taylm.Real.Operations.Minus
public import CORALean.ContSet.Taylm.Real.Operations.OptBnb
public import CORALean.ContSet.Taylm.Real.Operations.OptBnbAdv
public import CORALean.ContSet.Taylm.Real.Operations.OptLinQuad
public import CORALean.ContSet.Taylm.Real.Operations.Plus
public import CORALean.ContSet.Taylm.Real.Operations.PolyBounds
public import CORALean.ContSet.Taylm.Real.Operations.PolyBoxBounds
public import CORALean.ContSet.Taylm.Real.Operations.Pow
public import CORALean.ContSet.Taylm.Real.Operations.PowBounds
public import CORALean.ContSet.Taylm.Real.Operations.ProdBounds
public import CORALean.ContSet.Taylm.Real.Operations.QfbLower
public import CORALean.ContSet.Taylm.Real.Operations.QuadTerms
public import CORALean.ContSet.Taylm.Real.Operations.RangeBound
public import CORALean.ContSet.Taylm.Real.Operations.Rdivide
public import CORALean.ContSet.Taylm.Real.Operations.Reach
public import CORALean.ContSet.Taylm.Real.Operations.ReexpBoxBounds
public import CORALean.ContSet.Taylm.Real.Operations.ReexpTerms
public import CORALean.ContSet.Taylm.Real.Operations.Reexpand
public import CORALean.ContSet.Taylm.Real.Operations.Sin
public import CORALean.ContSet.Taylm.Real.Operations.Sinh
public import CORALean.ContSet.Taylm.Real.Operations.Smul
public import CORALean.ContSet.Taylm.Real.Operations.SplitAt
public import CORALean.ContSet.Taylm.Real.Operations.Sqrt
public import CORALean.ContSet.Taylm.Real.Operations.Tan
public import CORALean.ContSet.Taylm.Real.Operations.Tanh
public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Operations.TermBounds
public import CORALean.ContSet.Taylm.Real.Operations.TermBoxBounds
public import CORALean.ContSet.Taylm.Real.Operations.Times
public import CORALean.ContSet.Taylm.Real.Operations.SupportBound
public import CORALean.ContSet.Taylm.Real.Operations.Trace
public import CORALean.ContSet.Taylm.Real.Operations.Prod
public import CORALean.ContSet.Taylm.Real.Operations.Det
public import CORALean.ContSet.Taylm.Real.Operations.WidestCoord
public import CORALean.ContSet.Taylm.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.Taylm.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Taylm.Real.Operations.BernsteinBasis
public import CORALean.ContSet.Taylm.Real.Operations.BernsteinEntry
public import CORALean.ContSet.Taylm.Real.Operations.BernsteinDegree
public import CORALean.ContSet.Taylm.Real.Operations.BernsteinCoeff
public import CORALean.ContSet.Taylm.Real.Operations.OptBernstein
public import CORALean.ContSet.Taylm.Real.Operations.QfbSearchStep

/-!
# Taylor model operations, collected

CORA's arithmetic on `taylm` (`plus`, `minus`, `uminus`, `uplus`, `times`, `mtimes`, `sum`,
`power`), the range bound `bounds` of `interval`, and the elementary functions `exp`, `log`,
`sqrt`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `tan`, `atan`, `asin`, `acos`, `inv`, `invSqrt`, all
`taylor` at their own derivative bound, itself `compose`. Beyond CORA: the antiderivative
`antideriv` (and the source's printed `antiderivPrinted`), a code list's run `codeEval` with
`intrinsic`, and range bounding `rangeBound`.
-/
