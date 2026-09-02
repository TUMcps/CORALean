import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# What `HPolytope` instantiates

`ContSet`, and `Reduce` as the identity: CORA's `compact` drops redundant
halfspaces and keeps the set exactly, so doing nothing is the sound stand-in
until that algorithm is written.

Not `Plus`, `LinComb` or `Mtimes`, and the obstacle is the class shape rather
than a missing operation: `Operations` computes all three. Each of `plusOf`,
`linCombOf` and `mtimesOf` takes the directions the result is described on and a
`SupportBound` in each of them, and `plus : S → S → S` has room for neither.
Filling them in here would mean solving one linear program per direction, and
nothing in this project solves one — `Global.LinProg` consumes a dual solution
and turns it into a proof, which is what keeps an unverified solver outside the
trusted base. So the operations stay named and the caller names its directions.

`OfInterval` is the one class a halfspace description could instantiate as it
stands, `Interval.hPolytope` being exact. It is not instantiated: the class
lives in `Conversion`, so the instance would put every importer of `OfInterval`
behind `HPolytope`, and on its own it still would not run a jump — that needs
`Plus` and `Mtimes` as well.

`and`, `comap`, `mapEquiv` and `translate` stay named operations for the
opposite reason: each is exact and there is no class to instantiate. That is
what a constrained zonotope's coefficient domain is built from.
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
