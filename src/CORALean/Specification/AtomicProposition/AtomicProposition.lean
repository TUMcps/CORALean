module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Atomic propositions

CORA's `atomicProposition` (`specification/atomicProposition.m`): a representation `set` of the
states for which a proposition holds, the coordinates `dims` of the ambient space it is a set of,
and the locations `locs` of a hybrid automaton it is restricted to (empty: all of them).
`set` lives in `S k`, a `k`-dimensional representation, and `dims` picks a coordinate of the `n`
ambient ones for each of its `k`; CORA does not check `dims` against `dim(set)`, here the length is
the type. `k` is a field, so propositions of different dimensions share a type.
The set of states where the proposition holds is [1, Sec. 3 (predicate)]'s `⟦a⟧`.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- An atomic proposition: a set of `k`-dimensional states, the coordinates of the ambient space it
constrains, and the locations it is restricted to (empty: all). -/
structure AtomicProposition (S : ℕ → Type) (n : ℕ) where
  k : ℕ
  set : S k
  dims : Fin k → Fin n
  locs : List ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
