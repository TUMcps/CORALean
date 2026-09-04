import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# What `HPolytope` instantiates

`ContSet`, and `Reduce` as the identity: CORA's `compact` drops redundant
halfspaces and keeps the set exactly, so doing nothing is the sound stand-in
until that algorithm is written.

Not `Plus`, `LinComb` or `Mtimes`, though `plusOf`, `linCombOf` and `mtimesOf`
all compute. Closing over their directions and support bounds — the way
`Ellipsoid.plusInstance` closes over its scaling — would need bounds for *every*
polytope, `plus : S → S → S` being total and a recursive algorithm summing sets
the caller never sees. That oracle does not exist: a description with no rows
denotes the whole space, unbounded in every non-zero direction. A useful `Plus`
here needs a type excluding unbounded sets first.

`OfInterval` could be instantiated as it stands, `Interval.hPolytope` being
exact, but the class lives in `Conversion`, so the instance would put every
importer of `OfInterval` behind `HPolytope`. `and`, `comap`, `mapEquiv` and
`translate` stay named operations: each is exact and there is no class for it.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

instance : ContSet (HPolytope α) α := ⟨HPolytope.construct⟩

instance : Reduce (HPolytope α) α where
  reduce P _ := P
  reduce_outer _ _ := subset_rfl

end CORALean.Real
