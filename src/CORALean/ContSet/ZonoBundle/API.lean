import CORALean.ContSet.ZonoBundle.Real.API
import CORALean.ContSet.ZonoBundle.Float.API

/-!
# Zonotope bundles, both layers

CORA's `zonoBundle` [1, §3.5.5]: a finite family of zonotopes, denoting their
intersection, exactly — the representation §3.5.5 introduces because a
zonotope is not closed under intersection.

The specification in `Real`, and in `Float` the same family at float zonotopes.
Nothing rounds at the bundle level: `intersection` appends and `reduce` forgets, while
`plus`, `linComb` and `mtimes` hand each member to its own float operation, so
every error box in sight is a member's.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010, §3.5.5.
-/
