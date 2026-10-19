module

public import CORALean.Specification.ReachSetAnalyzer.Theorems.AnalyzeTreeComplete
public import CORALean.Specification.ReachSetAnalyzer.Operations.Analyze
public import CORALean.Specification.ReachSetAnalyzer.Theorems.BranchProper
public import CORALean.Specification.ReachSetAnalyzer.Theorems.SignalsSoundOfBranch

@[expose] public section

/-!
# `analyze` analyzes every branch

For an analyzer made by the constructor and a tree of reach sets whose time intervals are proper,
every branch of the tree, from the root to a leaf, has an element in the result of
`analyze(obj,R)` that is sound for it. CORA's `analyze` drops the branches after the first at
every fork (`analyzeTreeCora`).
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyze_complete (aps : List (String × AtomicProposition S n)) (dur : ℝ)
    (masks : List (String × FiniteSignal ℝ Bool)) (hd : 0 ≤ dur) (hnd : (aps.map Prod.fst).Nodup)
    (R : List (ReachSetAnalyzer.Entry S n))
    (hR : ∀ e ∈ R, ∀ s ∈ e.timeInterval, s.time.inf < s.time.sup)
    (outs : List (List (String × FiniteSignal ℝ Kleene))) : -- --- CONCL ---
    ∀ obj ∈ ReachSetAnalyzer.mk? aps dur masks,
      obj.analyze (𝕋 := 𝕋) R = some outs →
      ∀ w, ReachSetAnalyzer.Branch (ReachSetAnalyzer.children R) 0 w →
        ∃ out ∈ outs, obj.SignalsSound dur R w out := by -- --- PROOF ---
  intro obj (hobj : ReachSetAnalyzer.mk? aps dur masks = some obj) h
  obtain ⟨obj0, hmk, -, -, hr⟩ := (ReachSetAnalyzer.mk?_spec aps dur masks).2 hd hnd
  have hobj0 : obj = obj0 := Option.some.inj (hobj.symm.trans hmk)
  subst hobj0
  intro w hw
  obtain ⟨out, hout, obj', hf, hsig⟩ := ReachSetAnalyzer.analyzeTree_complete _ _ _ _ _ _ _ h w hw
  exact ⟨out, hout, ReachSetAnalyzer.signalsSound_of_branch (𝕋 := 𝕋) obj dur hr R w
    (ReachSetAnalyzer.branch_proper R hR w hw) obj' hf out hsig⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
