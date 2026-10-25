module

public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# Zonotope bundles: the representation

CORA's `zonoBundle` [1, Def. 4]: a finite family of zonotopes, denoting their *intersection*, which
two zonotopes generally do not form a zonotope; a bundle keeps it exact instead of enclosing it.
`k = 0` denotes the empty intersection, `univ`, the whole space and not `∅` (unlike `VPolytope`'s
zero vertices), which is why `CompactSet` cannot be an unconditional instance. A bundle is the
general `SetIntersection` of its members (`toSetIntersection`, in CORA's order), and `construct` is
that intersection by definition, so what holds of every intersection is proved once there. The
fields stay CORA's, `parallelSets` as `k` and the cell array `Z` as `Fin k → _`. Over any real
module, as `Zonotope` is.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
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

/-- A zonotope bundle: `k` zonotopes, denoting their intersection; `k = 0` is the whole space. -/
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
