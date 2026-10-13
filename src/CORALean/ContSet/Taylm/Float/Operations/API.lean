module

public import CORALean.ContSet.Taylm.Float.Operations.BoxMid
public import CORALean.ContSet.Taylm.Float.Operations.BoxRad
public import CORALean.ContSet.Taylm.Float.Operations.ReexpBoxBounds
public import CORALean.ContSet.Taylm.Float.Operations.OptBnbAdv
public import CORALean.ContSet.Taylm.Float.Operations.PowBounds
public import CORALean.ContSet.Taylm.Float.Operations.ProdBounds
public import CORALean.ContSet.Taylm.Float.Operations.TermBoxBounds
public import CORALean.ContSet.Taylm.Float.Operations.PolyBoxBounds
public import CORALean.ContSet.Taylm.Float.Operations.InBox
public import CORALean.ContSet.Taylm.Float.Operations.Covers
public import CORALean.ContSet.Taylm.Float.Operations.HalveBox
public import CORALean.ContSet.Taylm.Float.Operations.WidestCoord
public import CORALean.ContSet.Taylm.Float.Operations.SplitAt
public import CORALean.ContSet.Taylm.Float.Operations.ListMax
public import CORALean.ContSet.Taylm.Float.Operations.ListMin
public import CORALean.ContSet.Taylm.Float.Operations.ArgMaxIdx
public import CORALean.ContSet.Taylm.Float.Operations.BnbStep
public import CORALean.ContSet.Taylm.Float.Operations.BnbLoop
public import CORALean.ContSet.Taylm.Float.Operations.BranchAndBound
public import CORALean.ContSet.Taylm.Float.Operations.OptBnb
public import CORALean.ContSet.Taylm.Float.Operations.RepresentsaEmptySet
public import CORALean.ContSet.Taylm.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Taylm.Float.Operations.GetSyms
public import CORALean.ContSet.Taylm.Float.Operations.Mmul
public import CORALean.ContSet.Taylm.Float.Operations.Mpower
public import CORALean.ContSet.Taylm.Float.Operations.Rdivide
public import CORALean.ContSet.Taylm.Float.Operations.Inv
public import CORALean.ContSet.Taylm.Float.Operations.InvBound
public import CORALean.ContSet.Taylm.Float.Operations.InvCoef
public import CORALean.ContSet.Taylm.Float.Operations.BelowPow
public import CORALean.ContSet.Taylm.Float.Operations.Bounds
public import CORALean.ContSet.Taylm.Float.Operations.CodeEval
public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Taylm.Float.Operations.Const
public import CORALean.ContSet.Taylm.Float.Operations.Empty
public import CORALean.ContSet.Taylm.Float.Operations.ConstCoef
public import CORALean.ContSet.Taylm.Float.Operations.Exp
public import CORALean.ContSet.Taylm.Float.Operations.Intrinsic
public import CORALean.ContSet.Taylm.Float.Operations.Log
public import CORALean.ContSet.Taylm.Float.Operations.Hyperbolic
public import CORALean.ContSet.Taylm.Float.Operations.RangeBound
public import CORALean.ContSet.Taylm.Float.Operations.Sinh
public import CORALean.ContSet.Taylm.Float.Operations.Cosh
public import CORALean.ContSet.Taylm.Float.Operations.LogCoef
public import CORALean.ContSet.Taylm.Float.Operations.TrigCoef
public import CORALean.ContSet.Taylm.Float.Operations.UnitRemainder
public import CORALean.ContSet.Taylm.Float.Operations.Sin
public import CORALean.ContSet.Taylm.Float.Operations.Cos
public import CORALean.ContSet.Taylm.Float.Operations.Minus
public import CORALean.ContSet.Taylm.Float.Operations.Mtimes
public import CORALean.ContSet.Taylm.Float.Operations.Plus
public import CORALean.ContSet.Taylm.Float.Operations.PolyBounds
public import CORALean.ContSet.Taylm.Float.Operations.Pow
public import CORALean.ContSet.Taylm.Float.Operations.Smul
public import CORALean.ContSet.Taylm.Float.Operations.Sum
public import CORALean.ContSet.Taylm.Float.Operations.TermBounds
public import CORALean.ContSet.Taylm.Float.Operations.Times
public import CORALean.ContSet.Taylm.Float.Operations.Uminus
public import CORALean.ContSet.Taylm.Float.Operations.Uplus
public import CORALean.ContSet.Taylm.Float.Operations.BoundDot
public import CORALean.ContSet.Taylm.Float.Operations.Tan
public import CORALean.ContSet.Taylm.Float.Operations.Tanh
public import CORALean.ContSet.Taylm.Float.Operations.Trace
public import CORALean.ContSet.Taylm.Float.Operations.Prod
public import CORALean.ContSet.Taylm.Float.Operations.Det
public import CORALean.ContSet.Taylm.Float.Operations.Taylor
public import CORALean.ContSet.Taylm.Float.Operations.MagUp
public import CORALean.ContSet.Taylm.Float.Operations.Atan
public import CORALean.ContSet.Taylm.Float.Operations.ArcsinCoef
public import CORALean.ContSet.Taylm.Float.Operations.ArcsinBound
public import CORALean.ContSet.Taylm.Float.Operations.Asin
public import CORALean.ContSet.Taylm.Float.Operations.Acos
public import CORALean.ContSet.Taylm.Float.Operations.SqrtCoef
public import CORALean.ContSet.Taylm.Float.Operations.SqrtBound
public import CORALean.ContSet.Taylm.Float.Operations.Sqrt
public import CORALean.ContSet.Taylm.Float.Operations.BinomCoef
public import CORALean.ContSet.Taylm.Float.Operations.BernsteinStep
public import CORALean.ContSet.Taylm.Float.Operations.BernsteinEntryBounds
public import CORALean.ContSet.Taylm.Float.Operations.BoundsProd
public import CORALean.ContSet.Taylm.Float.Operations.BernsteinCoeffBounds
public import CORALean.ContSet.Taylm.Float.Operations.BernsteinIdx
public import CORALean.ContSet.Taylm.Float.Operations.OptBernstein
public import CORALean.ContSet.Taylm.Float.Operations.ReexpPairs
public import CORALean.ContSet.Taylm.Float.Operations.ReexpCoef
public import CORALean.ContSet.Taylm.Float.Operations.ReexpandAt
public import CORALean.ContSet.Taylm.Float.Operations.Reexpand

/-!
# Float Taylor model operations, collected

The exact layer's arithmetic with each coefficient computation enclosed and its width added
to the remainder, and `exp` and `log` with every constant of their expansions enclosed.
`codeEval` runs a code list with them, and `rangeBound` bounds its range over a box.
-/
