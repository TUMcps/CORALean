import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# What `HPolytope` instantiates

`ContSet`, and `Reduce` as the identity: CORA's `compact` drops redundant
halfspaces and keeps the set exactly, so doing nothing is the sound stand-in
until that algorithm is written.

Not `Plus` or `LinComb` — neither is computable here without enumerating
vertices first, so the representation instantiates neither and owes nothing.
`and`, `comap`, `mapEquiv` and `translate` stay named operations, which is what
a constrained zonotope's coefficient domain is built from.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

instance : ContSet (HPolytope α) α := ⟨HPolytope.construct⟩

instance : Reduce (HPolytope α) α where
  reduce P _ := P
  reduce_outer _ _ := subset_rfl

end CORALean.Real
