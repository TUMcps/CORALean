module

public import CORALean.ContSet.SetIntersection.SetIntersection
public import CORALean.ContSet.SetIntersection.Operations.API
public import CORALean.ContSet.SetIntersection.Theorems.API
public import CORALean.ContSet.SetIntersection.Instances

/-!
# The intersection of a list of representations, collected

`SetIntersection S` denotes `⋂ s ∈ sets, construct s` at whatever `S`
denotes, `univ` at the empty list — the same idea `ZonoBundle` fixes at one
member type and one arity, generalized to any `S` and any list length.
`Operations/` maps a member's own `Mtimes`, `Plus` or `Reduce` over the
branches; `Theorems/` proves each stays outer; `Instances.lean` turns those
proofs into the classes an algorithm asks for.

Every guarantee here is outer, unlike `SetUnion`'s `mtimes`: an intersection
only ever shrinks under a branch-wise bound, `⋂ M Sᵢ` covering `M (⋂ Sᵢ)`
rather than equalling it, even where every branch's own operation is exact.
-/
