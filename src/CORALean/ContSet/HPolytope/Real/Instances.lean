import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.ContSet.HPolytope.Real.Theorems.AndExact
import CORALean.ContSet.HPolytope.Real.Theorems.MapEquivExact

/-!
# What `HPolytope` instantiates

`ContSet`, and `Reduce` as the identity: CORA's `compact` drops redundant
halfspaces and keeps the set exactly, so doing nothing is the sound stand-in
until that algorithm is written.

Not `Plus`, `LinComb` or `Mtimes`, though `plusOf`, `linCombOf` and `mtimesOf`
all compute. Closing over their directions and support bounds — the way
`Ellipsoid.plusInstance` closes over its scalings — would need bounds for *every*
polytope, `plus : S → S → S` being total and a recursive algorithm summing sets
the caller never sees. That oracle does not exist: a description with no rows
denotes the whole space, unbounded in every non-zero direction. A useful `Plus`
here needs a type excluding unbounded sets first.

`OfInterval` could be instantiated as it stands, `Interval.hPolytope` being
exact, but the class lives in `Conversion`, so the instance would put every
importer of `OfInterval` behind `HPolytope`. `And` now lands too, at any real
module; `mapEquiv` backs `Reindex` below, and `comap`, `translate` stay named.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (HPolytope α) α := ⟨HPolytope.construct⟩

instance : Reduce (HPolytope α) α where
  reduce P _ := P
  reduce_outer _ _ := subset_rfl

instance : And (HPolytope α) α where
  and := HPolytope.and
  and_outer P₁ P₂ := (HPolytope.and_exact P₁ P₂).subset

/-- `mapEquiv` wants an equivalence, not a linear map, so a reindexing goes
through `LinearEquiv.funCongrLeft`, whose coercion is `reindexLin` again. -/
instance : Reindex (fun n => HPolytope (Vec ℝ n)) where
  reindex e P := HPolytope.mapEquiv (LinearEquiv.funCongrLeft ℝ ℝ e) P
  reindex_exact e P := (HPolytope.mapEquiv_exact (LinearEquiv.funCongrLeft ℝ ℝ e) P).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
