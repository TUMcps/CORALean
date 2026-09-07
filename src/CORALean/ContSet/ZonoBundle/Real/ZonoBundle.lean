import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Zonotope bundles: the representation

CORA's `zonoBundle` [1, §3.5.5]: a finite family of zonotopes, denoting their
*intersection*. Two zonotopes generally do not intersect in a zonotope, so a
bundle is what lets an algorithm keep such an intersection exact instead of
enclosing it back into a single one.

`k = 0` denotes an intersection over an empty family, which is `univ` — the
*whole space*, not `∅`. That is the opposite of `VPolytope`'s zero vertices,
and it is why `CompactSet` below cannot be an unconditional instance: `univ`
is compact only in the trivial ambient type.

Over any real module, as `Zonotope` is: nothing about an intersection of sets
mentions coordinates either.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010, §3.5.5.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

structure ZonoBundle (α : Type) where
  k : ℕ
  Z : Fin k → Zonotope α

def ZonoBundle.construct (zB : ZonoBundle α) : Set α := ⋂ i, (zB.Z i).construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
