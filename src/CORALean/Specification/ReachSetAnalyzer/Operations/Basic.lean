module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.Entry
public import CORALean.Specification.ReachSetAnalyzer.ReachSetAnalyzer

@[expose] public section

/-!
# `ReachSetAnalyzer/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- ===============================  `ReachSetAnalyzer.children`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `out = children(R,parent)` of `reachSet`: the indices `1,2,…` of the entries with that
parent. -/
def ReachSetAnalyzer.children (R : List (ReachSetAnalyzer.Entry S n)) (parent : ℕ) : List ℕ :=
  (List.range R.length).filterMap fun i =>
    if R[i]?.map (·.parent) = some parent then some (i + 1) else none


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
