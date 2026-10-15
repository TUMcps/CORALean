module

public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeSingle
public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeTree
public import CORALean.Specification.ReachSetAnalyzer.Operations.Signals

@[expose] public section

/-!
# The analysis of a tree of reach sets

`out = analyze(obj,R)` (`i = 0`): the signals of every branch of the reach set `R`, a list of
`reachSet`s that form a tree by their `parent`. CORA's `analyze` is not what its comment says: its
loop analyzes the children `c(1),…,c(end-1)` on copies and then `c(1)` again on `obj`, so with two
children the second never is analyzed; this is `analyzeTreeCora`. The definition here analyzes
every child, as the comment ("use the current copy for last child") means.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `out = analyze(obj,R)`. -/
noncomputable def ReachSetAnalyzer.analyze (obj : ReachSetAnalyzer S n)
    (R : List (ReachSetAnalyzer.Entry S n)) :
    Option (List (List (String × FiniteSignal ℝ Kleene))) :=
  ReachSetAnalyzer.analyzeTree (ReachSetAnalyzer.children R)
    (fun o j => (R[j - 1]?).bind fun e => o.analyzeSingle (𝕋 := 𝕋) e) ReachSetAnalyzer.signals
    (R.length + 1) 0 obj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
