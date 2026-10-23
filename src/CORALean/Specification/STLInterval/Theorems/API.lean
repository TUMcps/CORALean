module

public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.ContainsPointZeroIff
public import CORALean.Specification.STLInterval.Theorems.ContainsZeroIff
public import CORALean.Specification.STLInterval.Theorems.InfimumClosedIff
public import CORALean.Specification.STLInterval.Theorems.InfimumValue
public import CORALean.Specification.STLInterval.Theorems.IsequalZeroIff
public import CORALean.Specification.STLInterval.Theorems.MaximalRunsCongr
public import CORALean.Specification.STLInterval.Theorems.NonemptySetSubsetIff
public import CORALean.Specification.STLInterval.Theorems.NotMemBoundsOfEmptyBounds
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.RawSetBoundsNe
public import CORALean.Specification.STLInterval.Theorems.RawSetClamp
public import CORALean.Specification.STLInterval.Theorems.RawSetClampMono
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerOfGe
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerReach
public import CORALean.Specification.STLInterval.Theorems.RawSetMinkDiff
public import CORALean.Specification.STLInterval.Theorems.RawSetMono
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOf
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.RawSetOrdConnected
public import CORALean.Specification.STLInterval.Theorems.RawSetSub
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperOfLe
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperReach
public import CORALean.Specification.STLInterval.Theorems.RepresentsaEmptySetIff
public import CORALean.Specification.STLInterval.Theorems.RepresentsaOriginZeroIff
public import CORALean.Specification.STLInterval.Theorems.RepresentsaPointZeroIff
public import CORALean.Specification.STLInterval.Theorems.SetAnd
public import CORALean.Specification.STLInterval.Theorems.SetClamp
public import CORALean.Specification.STLInterval.Theorems.SetEqSingletonIff
public import CORALean.Specification.STLInterval.Theorems.SetIffMemBounds
public import CORALean.Specification.STLInterval.Theorems.SetInjective
public import CORALean.Specification.STLInterval.Theorems.SetInterval
public import CORALean.Specification.STLInterval.Theorems.SetLeftClosure
public import CORALean.Specification.STLInterval.Theorems.SetMinkDiff
public import CORALean.Specification.STLInterval.Theorems.SetMinkDiffOuter
public import CORALean.Specification.STLInterval.Theorems.SetMinus
public import CORALean.Specification.STLInterval.Theorems.SetMinusInterval
public import CORALean.Specification.STLInterval.Theorems.SetMinusIntervalOuter
public import CORALean.Specification.STLInterval.Theorems.SetMinusNum
public import CORALean.Specification.STLInterval.Theorems.SetMinusNumOuter
public import CORALean.Specification.STLInterval.Theorems.SetMinusOuter
public import CORALean.Specification.STLInterval.Theorems.SetOrdConnected
public import CORALean.Specification.STLInterval.Theorems.SetPlus
public import CORALean.Specification.STLInterval.Theorems.SetPlusInterval
public import CORALean.Specification.STLInterval.Theorems.SetPlusIntervalOuter
public import CORALean.Specification.STLInterval.Theorems.SetPlusNum
public import CORALean.Specification.STLInterval.Theorems.SetPlusNumOuter
public import CORALean.Specification.STLInterval.Theorems.SetPlusOuter
public import CORALean.Specification.STLInterval.Theorems.SetRightClosure
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.SetStlIntervalBounds
public import CORALean.Specification.STLInterval.Theorems.SetToLeft
public import CORALean.Specification.STLInterval.Theorems.SetToRight
public import CORALean.Specification.STLInterval.Theorems.StlIntervalBoundsToRealInterval
public import CORALean.Specification.STLInterval.Theorems.StlIntervalToRealInterval
public import CORALean.Specification.STLInterval.Theorems.SupremumClosedIff
public import CORALean.Specification.STLInterval.Theorems.SupremumValue
public import CORALean.Specification.STLInterval.Theorems.ToERealMapAddUpGe
public import CORALean.Specification.STLInterval.Theorems.ToERealMapSubUpGe
public import CORALean.Specification.STLInterval.Theorems.WithinTolZero
public import CORALean.Specification.STLInterval.Theorems.ZeroLeAddCoe
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet

/-!
# STL intervals: the theorems

Each method denotes the set of times its documentation names (`set_and_`, `set_plus`, `set_minus`,
`set_minkDiff`, ...), `contains_`, `isequal` and `representsa_` agree with it at tolerance zero, and
`set_injective` makes the normal form canonical. `minkDiffCora_counterexample` is the one place
CORA's code departs from its documentation. The `rawSet_…` files are the bounds-level lemmas.
-/
