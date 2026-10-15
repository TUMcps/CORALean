module

public import CORALean.Specification.AtomicProposition.AtomicProposition
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode

@[expose] public section

/-!
# Incremental verification of an STL formula on reachable sets

CORA's `onlineReachSetAnalyzer` (`specification/onlineReachSetAnalyzer.m`): the syntax DAG of an
STL formula, one `onlineAnalyzerNode` per distinct subformula (`nodes`, numbered from `1`, the
root first), whose leaves (`true`, `false`, atomic propositions) observe the reachable sets as they
arrive and whose other nodes combine what their children know (`propagate`). `leaves` are the
indices of the leaf nodes, `numObservations` counts the observations and `propagated` records
the nodes already visited by the current propagation. CORA's analyzer is a handle object that
its methods mutate; here a method returns the new analyzer. `S n` is the set representation the
atomic propositions are stated in, `d` the dimension of the observed sets.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure OnlineReachSetAnalyzer (S : ℕ → Type) (d : ℕ) where
  propagationFrequency : ℕ
  nodes : List (OnlineAnalyzerNode (AtomicProposition S d))
  leaves : List ℕ
  numObservations : ℕ
  propagated : List Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
