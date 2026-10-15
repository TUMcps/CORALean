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
object that its methods mutate; here a method returns the new analyzer.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure ReachSetAnalyzer (S : ℕ → Type) (n : ℕ) where
  aps : List (String × AtomicProposition S n)
  sigBuilder : List (String × FiniteKleeneSignalBuilder)
  masks : List (String × FiniteSignal ℝ Bool)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
