import CORALean.ContSet.ZonoBundle.Real.API

/-!
# Zonotope bundles

CORA's `zonoBundle` [1, §3.5.5]: a finite family of zonotopes, denoting their
intersection, exactly — the representation §3.5.5 introduces because a
zonotope is not closed under intersection.

Real layer only: nothing here rounds, `and` being generator concatenation and
`plus`/`mtimes` an outer approximation already at every real generator.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010, §3.5.5.
-/
