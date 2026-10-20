module

public import CORALean.Specification.ReachSetAnalyzer.Theorems.AnalyzeTreeSound
public import CORALean.Specification.ReachSetAnalyzer.Operations.Analyze
public import CORALean.Specification.ReachSetAnalyzer.Theorems.BranchProper
public import CORALean.Specification.ReachSetAnalyzer.Theorems.SignalsSoundOfBranch

@[expose] public section

/-!
# `analyze` is sound

For an analyzer made by the constructor and a tree of reach sets whose time intervals are proper,
each element of `analyze(obj,R)` is a list of signals that is sound (`SignalsSound`) for the
sets of one branch of the tree, from the root to a leaf. A signal that is true at `t` says every
state of every set of the branch that covers `t` satisfies the proposition, one that is false
that none does.

## Inputs
* `aps` – labelled atomic propositions
* `dur` – signal duration
* `masks` – masks of the propositions
* `R` – tree of reach sets
* `outs` – results of the analysis

## Hypotheses
* `hd` – the duration is nonnegative
* `hnd` – the proposition keys are distinct
* `hR` – all time intervals are proper

## Conclusion
* every result is sound for its branch
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

theorem ReachSetAnalyzer.analyze_sound (aps : List (String × AtomicProposition S n)) (dur : ℝ)
    (masks : List (String × FiniteSignal ℝ Bool)) (hd : 0 ≤ dur) (hnd : (aps.map Prod.fst).Nodup)
    (R : List (ReachSetAnalyzer.Entry S n))
    (hR : ∀ e ∈ R, ∀ s ∈ e.timeInterval, s.time.inf < s.time.sup)
    (outs : List (List (String × FiniteSignal ℝ Kleene))) : -- --- CONCL ---
    ∀ obj ∈ ReachSetAnalyzer.mk? aps dur masks,
      obj.analyze (𝕋 := 𝕋) R = some outs →
      ∀ out ∈ outs, ∃ w, ReachSetAnalyzer.Branch (ReachSetAnalyzer.children R) 0 w ∧
        obj.SignalsSound dur R w out := by -- --- PROOF ---
  intro obj (hobj : ReachSetAnalyzer.mk? aps dur masks = some obj) h
  obtain ⟨obj0, hmk, -, -, hr⟩ := (ReachSetAnalyzer.mk?_spec aps dur masks).2 hd hnd
  have hobj0 : obj = obj0 := Option.some.inj (hobj.symm.trans hmk)
  subst hobj0
  intro out hout
  obtain ⟨w, obj', hw, hf, hsig⟩ := ReachSetAnalyzer.analyzeTree_sound _ _ _ _ _ _ _ h out hout
  exact ⟨w, hw, ReachSetAnalyzer.signalsSound_of_branch (𝕋 := 𝕋) obj dur hr R w
    (ReachSetAnalyzer.branch_proper R hR w hw) obj' hf out hsig⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
