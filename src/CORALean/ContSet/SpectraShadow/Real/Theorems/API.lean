import CORALean.ContSet.SpectraShadow.Real.Theorems.LmiAppend
import CORALean.ContSet.SpectraShadow.Real.Theorems.PosSemidefPlusIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.PlusExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.MtimesExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.CartProdExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.Convex
import CORALean.ContSet.SpectraShadow.Real.Theorems.EmptyExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.InfExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.A0AddSumEq
import CORALean.ContSet.SpectraShadow.Real.Theorems.ProjectExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.InterExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.IsBoundedIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.ContainsIffVertices
import CORALean.ContSet.SpectraShadow.Real.Theorems.ContainsPointCoraLine
import CORALean.ContSet.SpectraShadow.Real.Theorems.ContainsPointOfMem
import CORALean.ContSet.SpectraShadow.Real.Theorems.ContainsPointZeroIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.LeSupportFuncOfMem
import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleMem
import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleNotMem
import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleSum
import CORALean.ContSet.SpectraShadow.Real.Theorems.LmiOfAZero
import CORALean.ContSet.SpectraShadow.Real.Theorems.PointExampleConstruct
import CORALean.ContSet.SpectraShadow.Real.Theorems.PointExampleIsBounded
import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaEmptySetIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaFullspaceCoraLine
import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaOriginIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaPointIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncCoraAllZeroNeSupportFunc
import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqBotIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqOfComplementary
import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqTopOfUnbounded
import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncLeOfBound
import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncLeSupportBound
import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncNeTopIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.TraceLmiMul
import CORALean.ContSet.SpectraShadow.Real.Theorems.TraceMulNonneg

/-!
# What a spectrahedral shadow guarantees, collected

`plus`, `map`, `mtimes` and `cartProd` exactly, each as an equation of sets, and
convexity unconditionally. `lmi_append` and `posSemidef_plus_iff` say that `plus`'s
inequality is the two it came from, which the float layer reuses. Nothing here is an
enclosure: a spectrahedral shadow is closed under every operation computed here.
The support function is bounded by the dual certificate (`supportFunc_le_supportBound`, weak
duality) and equals it under complementary slackness; `isBounded`, `representsa_` at
`emptySet`, `origin` and `point`, and `containsPoint` at tolerance `0` are exact; and
`CoraCounterexamples` states three places where CORA's own code answers differently.
-/
