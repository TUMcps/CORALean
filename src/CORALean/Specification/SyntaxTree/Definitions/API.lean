module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.Dom
public import CORALean.Specification.SyntaxTree.Definitions.DomFloat
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.Definitions.IsBinarySound
public import CORALean.Specification.SyntaxTree.Definitions.IsBinarySoundFloat
public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySound
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySoundFloat
public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat

/-!
# Syntax trees: the definitions

`Dom.contains` and `Dom.IsWithin` for the intervals nodes store, `IsInBox` for a point of a box,
`Encloses`
(a node's interval encloses its function) and `IsSound` (every node does, with a `funHan` that is
sound
in the sense of `IsUnarySound` and `IsBinarySound`).
-/
