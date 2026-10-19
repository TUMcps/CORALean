module

public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# Zonotope bundles: the representation

CORA's `zonoBundle` [1, Def. 4]: a finite family of zonotopes, denoting their
*intersection*. Two zonotopes generally do not intersect in a zonotope, so a
bundle is what lets an algorithm keep such an intersection exact instead of
enclosing it back into a single one.

`k = 0` denotes an intersection over an empty family, which is `univ` — the *whole space*, not
`∅`, the opposite of `VPolytope`'s zero vertices — and is why `CompactSet` cannot be an
unconditional instance: `univ` is compact only in the trivial ambient type.

A bundle is the general `SetIntersection` of its members (`toSetIntersection`, the members
listed in CORA's order), and `construct` is that intersection by definition: what holds of every
intersection is proved once there, and `Theorems/` states only what CORA's own algorithms give
beyond it. The fields stay CORA's, `parallelSets` as `k` and the cell array `Z` as `Fin k → _`.

Over any real module, as `Zonotope` is: nothing about an intersection of sets
mentions coordinates either.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   18-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

structure ZonoBundle (α : Type) where
  k : ℕ
  Z : Fin k → Zonotope α

/-- The bundle as the general intersection of its members, listed in CORA's order. -/
def ZonoBundle.toSetIntersection (zB : ZonoBundle α) : SetIntersection (Zonotope α) :=
  ⟨List.ofFn zB.Z⟩

/-- What a bundle denotes: the intersection `SetIntersection` denotes, of its members. -/
def ZonoBundle.construct (zB : ZonoBundle α) : Set α := ContSet.construct zB.toSetIntersection

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
