module

public import CORALean.Specification.AtomicProposition.AtomicProposition
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Formula

@[expose] public section

/-!
# `OnlineReachSetAnalyzer/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ===========================  `OnlineReachSetAnalyzer.ParseState`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What `parse` changes: the nodes made so far, and `cache` from subformula key to node index. -/
structure OnlineReachSetAnalyzer.ParseState (𝕋 : Type) [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] (S : ℕ → Type) (d : ℕ) where
  nodes : List (OnlineAnalyzerNode 𝕋 (AtomicProposition S d))
  cache : List (OnlineReachSetAnalyzer.Formula 𝕋 Unit × ℕ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
