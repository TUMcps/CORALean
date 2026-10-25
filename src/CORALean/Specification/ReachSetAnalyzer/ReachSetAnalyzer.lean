module

public import CORALean.Specification.AtomicProposition.AtomicProposition
public import CORALean.Specification.FiniteKleeneSignalBuilder.FiniteKleeneSignalBuilder

@[expose] public section

/-!
# Three-valued signals of atomic propositions over reachable sets

CORA's `reachSetAnalyzer` (`specification/reachSetAnalyzer.m`): the sets reached in each time
interval are tested against atomic propositions, and for each proposition a
`finiteKleeneSignalBuilder` records where it can be true and where it can be false. The three
`containers.Map`s of CORA, keyed by the name of the proposition, are lists of pairs in the order of
`keys(aps)`; `aps` holds the propositions, `sigBuilder` their builders and `masks` the times at
which each one matters (a proposition without mask matters always). CORA's analyzer is a handle
object that its methods mutate; here a method returns the new analyzer. Time stamps are in a time
type `T`: ℝ, or the float scalar the reach sets were computed in, compared exactly.

## References

None: CORA's `reachSetAnalyzer`, a software class: no publication introduces it, and the CORA manual
page for it could not be read.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A reach set analyzer: named atomic propositions, for each a builder of the three-valued signal
of its truth, and masks restricting the signals. -/
structure ReachSetAnalyzer (T : Type) (S : ℕ → Type) (n : ℕ) where
  aps : List (String × AtomicProposition S n)
  sigBuilder : List (String × FiniteKleeneSignalBuilder T)
  masks : List (String × FiniteSignal T Bool)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
