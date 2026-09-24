import CORALean.ContSet.SetUnion.SetUnion
import CORALean.ContSet.SetUnion.Operations.API
import CORALean.ContSet.SetUnion.Theorems.API
import CORALean.ContSet.SetUnion.Instances

/-!
# The union of a list of representations, collected

`SetUnion S` denotes `⋃ s ∈ sets, construct s` at whatever `S` denotes, `∅` at
the empty list. `Operations/` maps a member's own `Mtimes`, `Plus` or `Reduce`
over the branches; `Theorems/` proves each is still outer, and that `mtimes`
is exact when every branch's own is; `Instances.lean` is what turns those
proofs into the classes an algorithm asks for.

Not `SetIntersection`, which denotes `univ` at the empty list and is outer
throughout rather than exact even at `Mtimes` — the two share no code, since a
union's guarantee comes from `⊇` at each branch and an intersection's from
`⊆`, the opposite direction at every step.
-/
