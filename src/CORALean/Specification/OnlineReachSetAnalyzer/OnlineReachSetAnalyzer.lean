module

public import CORALean.Specification.AtomicProposition.AtomicProposition
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode

@[expose] public section

/-!
# Incremental verification of an STL formula on reachable sets

CORA's `onlineReachSetAnalyzer` (`specification/onlineReachSetAnalyzer.m`, [1, Alg. 1]): the syntax
DAG of an STL formula, one `onlineAnalyzerNode` per distinct subformula (`nodes`, numbered from `1`,
the root first), whose leaves (`true`, `false`, atomic propositions) observe the reachable sets as
they arrive and whose other nodes combine what their children know (`propagate`). `leaves` are the
indices of the leaf nodes, `numObservations` counts the observations and `propagated` records the
nodes already visited by the current propagation. CORA's analyzer is a handle object that its
methods mutate; here a method returns the new analyzer. `S n` is the set representation the atomic
propositions are stated in, `d` the dimension of the observed sets, `𝕋` the time scalar.

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- An online reach set analyzer: the nodes of the syntax tree of an STL formula, its leaves, how
many observations were made, and which nodes have propagated. -/
structure OnlineReachSetAnalyzer (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    (S : ℕ → Type) (d : ℕ) where
  propagationFrequency : ℕ
  nodes : List (OnlineAnalyzerNode 𝕋 (AtomicProposition S d))
  leaves : List ℕ
  numObservations : ℕ
  propagated : List Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
