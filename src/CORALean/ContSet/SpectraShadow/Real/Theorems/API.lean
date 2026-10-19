module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.LmiAppend
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PosSemidefPlusIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PlusExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.MtimesExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.CartProdExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.Convex
public import CORALean.ContSet.SpectraShadow.Real.Theorems.EmptyExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.InfExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.Basic
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ProjectExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.InterExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.IsBoundedIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ContainsIffVertices
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ContainsPointZeroIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleMem
public import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleNotMem
public import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleSum
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PointExampleConstruct
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PointExampleIsBounded
public import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaEmptySetIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaOriginIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaPointIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqBotIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqOfComplementary
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqTopOfUnbounded
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncNeTopIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.TraceLmiMul
public import CORALean.ContSet.SpectraShadow.Real.Theorems.TraceMulNonneg
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ConeConstruct
public import CORALean.ContSet.SpectraShadow.Real.Theorems.EqBlockSum
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SingletonOneConstruct
public import CORALean.ContSet.SpectraShadow.Real.Theorems.HyperplaneOneConstruct
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ConvHullExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.OrExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.LinCombOuter
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatQuadForm
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatPosSemidefOfPos
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatPosSemidefZero
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatPosSemidefNecessary
public import CORALean.ContSet.SpectraShadow.Real.Theorems.TranslateMem
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PolytopeOuter
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PolytopeInner
public import CORALean.ContSet.SpectraShadow.Real.Theorems.IsFullDimIffAffineSpan
public import CORALean.ContSet.SpectraShadow.Real.Theorems.NotIsFullDimOfGZero
public import CORALean.ContSet.SpectraShadow.Real.Theorems.GenerateESumRepExact

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
`EncloseExact.lean` is deliberately not collected here: it states the generic `enclose` at the
instances, which this API feeds.
-/
