module

public import CORALean.ContSet.ZonoBundle.Real.API
public import CORALean.ContSet.ZonoBundle.Float.API

/-!
# Zonotope bundles, both layers

CORA's `zonoBundle` [1, Def. 4]: a finite family of zonotopes, denoting their
intersection, exactly — the representation introduced because a
zonotope is not closed under intersection.

The specification in `Real`, and in `Float` the same family at float zonotopes.
Nothing rounds at the bundle level: `intersection` appends and `reduce` forgets, while
`plus`, `linComb` and `mtimes` hand each member to its own float operation, so
every error box in sight is a member's.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/
