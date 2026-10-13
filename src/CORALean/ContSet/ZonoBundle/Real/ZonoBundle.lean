import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Zonotope bundles: the representation

CORA's `zonoBundle` [1, §3.5.5], [2, Def. 4]: a finite family of zonotopes, denoting their
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
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
