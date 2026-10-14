module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.BinarySound
public import CORALean.Specification.SyntaxTree.Definitions.Dom
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound

/-!
# Syntax trees: the definitions

`Dom.contains` and `Dom.within` for the intervals nodes store, `InBox` for a point of a box,
`Encloses`
(a node's interval encloses its function) and `Sound` (every node does, with a `funHan` that is
sound
in the sense of `UnarySound` and `BinarySound`).
-/
