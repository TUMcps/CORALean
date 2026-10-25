module

public import CORALean.Specification.STLInterval.Definitions.Contains
public import CORALean.Specification.STLInterval.Definitions.ContainsPoint
public import CORALean.Specification.STLInterval.Definitions.Endpoint
public import CORALean.Specification.STLInterval.Definitions.Fields
public import CORALean.Specification.STLInterval.Definitions.FieldsContainsPoint
public import CORALean.Specification.STLInterval.Definitions.Isequal
public import CORALean.Specification.STLInterval.Definitions.IsMaximalRuns
public import CORALean.Specification.STLInterval.Definitions.IsInBounds
public import CORALean.Specification.STLInterval.Definitions.Representsa
public import CORALean.Specification.STLInterval.Definitions.RepresentsaType
public import CORALean.Specification.STLInterval.Definitions.ToEReal
public import CORALean.Specification.STLInterval.Definitions.IsWithinTol

/-!
# STL intervals: the definitions

`IsWithinTol`, the tolerance test of CORA's comparisons, and the `Prop`s of `@stlInterval`
(`contains_`, `isequal`, `representsa_`) built on it; `Endpoint` is what `infimum` and `supremum`
return, and `Fields` the object CORA's code stores, `NaN` bounds included.
-/
