module

public import CORALean.Specification.AtomicProposition.Theorems.HoldsOfCanBeFalseEqFalse
public import CORALean.Specification.AtomicProposition.Theorems.NotHoldsOfCanBeTrueEqFalse
public import CORALean.Specification.ReachSetAnalyzer.Definitions.SignalsSound
public import CORALean.Specification.ReachSetAnalyzer.Theorems.AnalyzeBranchSpec
public import CORALean.Specification.ReachSetAnalyzer.Theorems.MkSpec
public import CORALean.Specification.ReachSetAnalyzer.Theorems.SignalsSpec

@[expose] public section

/-!
# The signals after a branch are sound

An analyzer made by the constructor, on entries whose time intervals are proper, gives sound signals
(`SignalsSound`) after the entries of a branch were analyzed one after the other. This is the
meaning of `canBeTrue` and `canBeFalse` carried through the builders: a time is true only if no set
covering it can be false, and false only if none can be true.

## Inputs
* `obj` – analyzer
* `d` – signal duration
* `R` – tree of reach sets
* `w` – branch entries
* `obj'` – analyzer after the branch
* `out` – signal of each proposition

## Hypotheses
* `hobj` – the analyzer represents nothing marked
* `hw` – the branch's entries have proper time intervals
* `hf` – analyzing the branch's entries gives the analyzer
* `hs` – the signals are those of the analyzer

## Conclusion
* the signals are sound for the branch
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.signalsSound_of_branch (obj : ReachSetAnalyzer S n) (d : ℝ)
    (hobj : obj.Represents d (fun _ _ => False) (fun _ _ => False))
    (R : List (ReachSetAnalyzer.Entry S n)) (w : List ℕ)
    (hw : ∀ j ∈ w, ∃ e, R[j - 1]? = some e ∧ ∀ s ∈ e.timeInterval, s.time.inf < s.time.sup)
    (obj' : ReachSetAnalyzer S n)
    (hf : w.foldlM (fun o j => (R[j - 1]?).bind fun e => o.analyzeSingle (𝕋 := 𝕋) e) obj =
      some obj') (out : List (String × FiniteSignal ℝ Kleene)) (hs : obj'.signals = some out)
    : -- --- CONCL ---
    obj.SignalsSound d R w out := by -- --- PROOF ---
  -- what the analyzer says after the branch, and what its signals say
  obtain ⟨o2, hf2, ha, hm, hr⟩ := ReachSetAnalyzer.analyzeBranch_spec (𝕋 := 𝕋) obj d R w hw
    (fun _ _ => False) (fun _ _ => False) obj rfl rfl hobj
  obtain rfl : o2 = obj' := Option.some.inj (hf2.symm.trans hf)
  obtain ⟨sigs, hsigs, hF⟩ := ReachSetAnalyzer.signals_spec o2 d _ _ hr
  obtain rfl : sigs = out := Option.some.inj (hsigs.symm.trans hs)
  intro k s hks ap hap
  -- the signal of key `k` is the one of the proposition at the same position
  have gen : ∀ {α β : Type} (P : α → β → Prop) (l1 : List α) (l2 : List β),
      List.Forall₂ P l1 l2 → ∀ q ∈ l2, ∃ p ∈ l1, P p q := by
    intro α β P l1 l2 h
    induction h with
    | nil => intro q hq; simp at hq
    | cons hpq _ ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨_, List.mem_cons_self, hpq⟩
      · obtain ⟨p, hp, hpq'⟩ := ih q hq
        exact ⟨p, List.mem_cons_of_mem _ hp, hpq'⟩
  obtain ⟨⟨pk, pap⟩, -, hpk, hv, hd, hat⟩ := gen _ _ _ hF (k, s) hks
  obtain rfl : k = pk := hpk
  refine ⟨hv, hd, fun t h0 h1 => ?_⟩
  obtain ⟨v, hvt, htt, hff⟩ := hat t h0 h1
  refine ⟨v, hvt, fun hvtt => ?_, fun hvff => ?_⟩
  · -- true: no covering set can be false
    have hnf := ((htt.mp hvtt).2)
    intro j hj e he st hst hmask hcov x hx
    refine AtomicProposition.holds_of_canBeFalse_eq_false (𝕋 := 𝕋) ap st.set e.loc ?_ hx
    by_contra hne
    exact hnf (Or.inr ⟨j, hj, e, he, st, hst, ap, hap, hmask, by simpa using hne, hcov⟩)
  · -- false: no covering set can be true
    have hnt := ((hff.mp hvff).2)
    intro j hj e he st hst hmask hcov x hx
    refine AtomicProposition.not_holds_of_canBeTrue_eq_false (𝕋 := 𝕋) ap st.set e.loc ?_ hx
    by_contra hne
    exact hnt (Or.inr ⟨j, hj, e, he, st, hst, ap, hap, hmask, by simpa using hne, hcov⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
