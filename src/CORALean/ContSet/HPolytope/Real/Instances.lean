import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# What `HPolytope` instantiates

`ContSet`, and `Reduce` as the identity: CORA's `compact` drops redundant
halfspaces and keeps the set exactly, so doing nothing is the sound stand-in
until that algorithm is written.

Not `Plus`, `LinComb` or `Mtimes`, and the reason is neither the class shape nor
a missing operation. `plusOf`, `linCombOf` and `mtimesOf` all compute; each
takes the directions the result is described on and a `SupportBound` in each,
and closing those over — the way `Ellipsoid.plusInstance` closes over its
scaling — would give a lawful `Plus` in three lines. What it would need is
bounds for *every* polytope, `plus : S → S → S` being total and a recursive
algorithm summing sets the caller never sees: `LinearSysDT.reach` at step `k+1`
names the set step `k` produced.

That oracle does not exist. A halfspace description with no rows denotes the
whole space, whose support function is unbounded in every non-zero direction, so
`∀ P i, SupportBound P.construct (Aq i)` is inhabited only where every `Aq i` is
zero — and there the result is the whole space, which is lawful and says
nothing. `Reduce`'s identity is the same kind of trivial answer and is kept
because it is *exact*; the whole space loses everything, so it is not. What a
useful `Plus` here needs first is a type excluding unbounded sets. A linear
program is what the bounded case would still want after that, and
`Global.LinProg` consumes a dual solution rather than producing one, which is
what keeps an unverified solver outside the trusted base.

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
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

instance : ContSet (HPolytope α) α := ⟨HPolytope.construct⟩

instance : Reduce (HPolytope α) α where
  reduce P _ := P
  reduce_outer _ _ := subset_rfl

end CORALean.Real
