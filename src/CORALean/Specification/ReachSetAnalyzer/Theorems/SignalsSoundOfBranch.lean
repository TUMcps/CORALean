module

public import CORALean.Specification.AtomicProposition.Theorems.HoldsOfCanBeFalseEqFalse
public import CORALean.Specification.AtomicProposition.Theorems.NotHoldsOfCanBeTrueEqFalse
public import CORALean.Specification.ReachSetAnalyzer.Definitions.SignalsSound
public import CORALean.Specification.ReachSetAnalyzer.Theorems.AnalyzeSingleSpec
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the entries of a branch record. -/
theorem ReachSetAnalyzer.aux_analyzeBranch_spec (obj : ReachSetAnalyzer S n) (d : ℝ)
    (R : List (ReachSetAnalyzer.Entry S n)) : -- --- CONCL ---
    ∀ (w : List ℕ), (∀ j ∈ w, ∃ e, R[j - 1]? = some e ∧
      ∀ s ∈ e.timeInterval, s.time.inf < s.time.sup) →
    ∀ (PT PF : String → ℝ → Prop) (obj0 : ReachSetAnalyzer S n), obj0.aps = obj.aps →
      obj0.masks = obj.masks → obj0.Represents d PT PF →
      ∃ obj', w.foldlM (fun o j => (R[j - 1]?).bind fun e => o.analyzeSingle (𝕋 := 𝕋) e) obj0 =
        some obj' ∧ obj'.aps = obj.aps ∧ obj'.masks = obj.masks ∧ obj'.Represents d
          (fun k t => PT k t ∨ ∃ j ∈ w, ∃ e, R[j - 1]? = some e ∧ ∃ s ∈ e.timeInterval,
            obj.TrueMark (𝕋 := 𝕋) k s.set e.loc s.time.inf s.time.sup d t)
          (fun k t => PF k t ∨ ∃ j ∈ w, ∃ e, R[j - 1]? = some e ∧ ∃ s ∈ e.timeInterval,
            obj.FalseMark (𝕋 := 𝕋) k s.set e.loc s.time.inf s.time.sup d t) := by -- --- PROOF ---
  intro w
  induction w with
  | nil =>
    intro _ PT PF obj0 ha hm hr
    exact ⟨obj0, rfl, ha, hm, ReachSetAnalyzer.represents_of_iff obj0 d hr (fun k t => by simp)
      (fun k t => by simp)⟩
  | cons j w ih =>
    intro hw PT PF obj0 ha hm hr
    -- the first entry, on the analyzer as it is
    obtain ⟨e, he, hproper⟩ := hw j List.mem_cons_self
    obtain ⟨obj1, h1, ha1, hm1, hr1⟩ := ReachSetAnalyzer.analyzeSingle_spec (𝕋 := 𝕋) obj0 d PT PF
      hr e hproper
    rw [(ReachSetAnalyzer.marks_congr (𝕋 := 𝕋) obj obj0 ha hm).1,
      (ReachSetAnalyzer.marks_congr (𝕋 := 𝕋) obj obj0 ha hm).2] at hr1
    -- and the others on what it leaves
    obtain ⟨obj', h2, ha2, hm2, hr2⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)) _ _ obj1
      (ha1.trans ha) (hm1.trans hm) hr1
    refine ⟨obj', ?_, ha2, hm2, ReachSetAnalyzer.represents_of_iff obj' d hr2
      (fun k t => ?_) (fun k t => ?_)⟩
    · rw [List.foldlM_cons, he, Option.bind_some, h1]
      exact h2
    -- the times marked as possibly true: those of the first step or of the others
    · constructor
      · rintro ((h | ⟨s, hs, hh⟩) | ⟨q, hq, e', he', hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, List.mem_cons_self, e, he, s, hs, hh⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, e', he', hh⟩
      · rintro (h | ⟨q, hq, e', he', hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hq with rfl | hq
          · obtain rfl : e' = e := Option.some.inj (he'.symm.trans he)
            exact Or.inl (Or.inr hh)
          · exact Or.inr ⟨q, hq, e', he', hh⟩
    -- the times marked as possibly false: likewise
    · constructor
      · rintro ((h | ⟨s, hs, hh⟩) | ⟨q, hq, e', he', hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, List.mem_cons_self, e, he, s, hs, hh⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, e', he', hh⟩
      · rintro (h | ⟨q, hq, e', he', hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hq with rfl | hq
          · obtain rfl : e' = e := Option.some.inj (he'.symm.trans he)
            exact Or.inl (Or.inr hh)
          · exact Or.inr ⟨q, hq, e', he', hh⟩


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
  obtain ⟨o2, hf2, ha, hm, hr⟩ := ReachSetAnalyzer.aux_analyzeBranch_spec (𝕋 := 𝕋) obj d R w hw
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
