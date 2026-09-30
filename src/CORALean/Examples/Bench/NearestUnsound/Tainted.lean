import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatOuter
import CORALean.Examples.Bench.NearestUnsound.Instances

/-!
# What the false axiom taints: the soundness theorem, instantiated here

`LinearSys.reachFloat_outer` holds at every `SoundFloatArithmetic` instance, so
Lean accepts it at `NearestFloat` too, and what it then says is worthless: the
instance's rounding laws are projections of `nearestUnsound`, the false axiom of
`Axioms`. These two copies exist for `scripts/check-axioms.sh`, which asserts
that each of them *does* depend on `nearestUnsound` — the positive control that
shows the check can see a taint at all — while the library's own
`reachFloat_outer`, stated for an arbitrary scalar, does not.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean.Bench.NearestUnsound


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reachFloat_outer` at `NearestFloat`, in the plane: accepted, and FALSE in
substance, since it rests on `nearestUnsound`. Never cite it. -/
theorem NearestUnsound.reachFloat_outer_nearestFloat :
    type_of% (@LinearSys.reachFloat_outer NearestFloat _ _ _ 2) :=
  @LinearSys.reachFloat_outer NearestFloat _ _ _ 2

/-- The same at `NearestDyadic 24`, round-to-nearest binary32, resting on
`nearestUnsound` too. Never cite it. -/
theorem NearestUnsound.reachFloat_outer_nearestDyadic :
    type_of% (@LinearSys.reachFloat_outer (NearestDyadic 24) _ _ _ 2) :=
  @LinearSys.reachFloat_outer (NearestDyadic 24) _ _ _ 2

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
