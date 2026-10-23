module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Global.FoldlMOptionMap
public import CORALean.Global.LookupMapSnd
public import CORALean.Global.MapMOptionMap
public import CORALean.Global.ReplaceKeyMapSnd
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.CombineMapTime
public import CORALean.Specification.FiniteSignal.Theorems.IndicatorMapTime
public import CORALean.Specification.FiniteSignal.Theorems.MaxSpec
public import CORALean.Specification.FiniteSignal.Theorems.MkMapTime
public import CORALean.Specification.ReachSetAnalyzer.Definitions.HasEnclosingTimes
public import CORALean.Specification.ReachSetAnalyzer.Operations.Analyze
public import CORALean.Specification.ReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.ReachSetAnalyzer.Theorems.AnalyzeTreeSound
public import CORALean.Specification.ReachSetAnalyzer.Theorems.BranchProper
public import CORALean.Specification.ReachSetAnalyzer.Theorems.MkSpec
public import CORALean.Specification.ReachSetAnalyzer.Theorems.SignalsSoundOfBranch

@[expose] public section

/-!
# `analyze` over float time stamps is sound for the exact time intervals

An analyzer over a float scalar `T` compares its time stamps exactly (`TimeOrder`), so every step of
`analyze` read through `toReal` is the real step on the reach sets read as reals, and each result is
sound for one branch of the tree in the sense of `analyze_sound`. A float reach set's time interval
encloses the exact one; the mask lets more through and a time is covered more often on the larger
interval, so a result that says true (false) at a time says it for the exact time intervals too:
every state of every set covering the time satisfies the proposition (none does).

## Inputs
* `aps` – labelled atomic propositions
* `dur` – signal duration
* `masks` – masks of the propositions
* `R` – tree of float reach sets
* `outs` – results of the analysis

## Hypotheses
* `hd` – the duration is nonnegative
* `hnd` – the proposition keys are distinct
* `hm` – the masks, read as reals, are valid
* `hR` – all time intervals are proper

## Conclusion
* every result, read as reals, is sound for its branch of any reach sets whose time intervals
  the float ones enclose
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {T : Type} [FloatOps T] [SoundFloatArithmetic T] [ExactLe T]
variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- A float mask's maximum on an interval is that of the mask read as reals. -/
theorem aux_max_mapTime (s : FiniteSignal T Bool) (lo hi : T) : -- --- CONCL ---
    (s.mapTime toReal).max (toReal lo) (toReal hi) = s.max lo hi := by -- --- PROOF ---
  unfold FiniteSignal.max FiniteSignal.mapTime FiniteSignal.length
  simp only [List.length_map]
  -- the first loop stops at the same breakpoint
  have hk : (List.takeWhile (fun t => decide (t < toReal lo)) (s.time.map toReal)).length =
      (List.takeWhile (fun t => decide (t < lo)) s.time).length := by
    rw [List.takeWhile_map, List.length_map]
    exact congrArg List.length (congrArg (List.takeWhile · s.time)
      (funext fun t => decide_eq_decide.mpr Iff.rfl))
  rw [hk]
  congr 1
  -- the second loop takes the same breakpoints
  funext v j
  have hg : (s.time.map toReal).getD j 0 = toReal (s.time.getD j 0) := by
    rw [← toReal_zero_eq (𝕋 := T), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases s.time[j]? <;> rfl
  rw [hg]
  by_cases h : s.time.getD j 0 ≤ hi
  · rw [if_pos h, if_pos (show toReal (s.time.getD j 0) ≤ toReal hi from h)]
  · rw [if_neg h, if_neg (show ¬ toReal (s.time.getD j 0) ≤ toReal hi from h)]

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- The mask of a float analyzer lets an interval through as its masks read as reals do. -/
theorem aux_maskOk_mapTime (obj : ReachSetAnalyzer T S n) (k : String)
    (lo hi : T) : -- --- CONCL ---
    (obj.mapTime toReal).maskOk k (toReal lo) (toReal hi) =
      obj.maskOk k lo hi := by -- --- PROOF ---
  unfold ReachSetAnalyzer.maskOk ReachSetAnalyzer.mapTime
  simp only
  rw [lookup_map_snd]
  cases obj.masks.lookup k with
  | none => rfl
  | some m => exact aux_max_mapTime m lo hi

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- A float builder's constructor, read as reals, is the real one. -/
theorem aux_builder_mk?_mapTime (dur : T) : -- --- CONCL ---
    (FiniteKleeneSignalBuilder.mk? dur).map (FiniteKleeneSignalBuilder.mapTime toReal) =
      FiniteKleeneSignalBuilder.mk? (toReal dur) := by -- --- PROOF ---
  have h := FiniteSignal.mk?_mapTime [dur] [false]
  simp only [List.map_cons, List.map_nil] at h
  unfold FiniteKleeneSignalBuilder.mk?
  rw [← h]
  cases FiniteSignal.mk? [dur] [false] <;> rfl

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- The constructor of a float analyzer, read as reals, is the real one. -/
theorem aux_mk?_mapTime (aps : List (String × AtomicProposition S n)) (dur : T)
    (masks : List (String × FiniteSignal T Bool)) : -- --- CONCL ---
    (ReachSetAnalyzer.mk? aps dur masks).map (ReachSetAnalyzer.mapTime toReal) =
      ReachSetAnalyzer.mk? aps (toReal dur)
        (masks.map fun p => (p.1, p.2.mapTime toReal)) := by -- --- PROOF ---
  unfold ReachSetAnalyzer.mk?
  have h := mapM_option_map (fun p : String × AtomicProposition S n =>
    (FiniteKleeneSignalBuilder.mk? dur).map fun b => (p.1, b))
    (fun p => (p.1, p.2.mapTime toReal)) aps
  simp only [Option.map_map] at h
  -- every builder is the float builder read as reals
  have h2 : (fun a : String × AtomicProposition S n => Option.map
      ((fun p => (p.1, FiniteKleeneSignalBuilder.mapTime toReal p.2)) ∘ fun b => (a.1, b))
      (FiniteKleeneSignalBuilder.mk? dur)) =
      fun a => (FiniteKleeneSignalBuilder.mk? (toReal dur)).map fun b => (a.1, b) := by
    funext a
    rw [← aux_builder_mk?_mapTime, Option.map_map]
    rfl
  rw [h2] at h
  rw [← h, Option.map_map, Option.map_map]
  rfl

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- Marking a float builder possibly true, read as reals, is the real marking. -/
theorem aux_setPossiblyTrue?_mapTime (obj : FiniteKleeneSignalBuilder T)
    (lo hi : T) : -- --- CONCL ---
    (obj.setPossiblyTrue? lo hi).map (FiniteKleeneSignalBuilder.mapTime toReal) =
      (obj.mapTime toReal).setPossiblyTrue? (toReal lo) (toReal hi) := by -- --- PROOF ---
  unfold FiniteKleeneSignalBuilder.setPossiblyTrue?
  dsimp only
  have hd : (obj.mapTime toReal).possiblyTrueSignal.duration =
      toReal obj.possiblyTrueSignal.duration :=
    FiniteSignal.duration_mapTime toReal toReal_zero_eq _
  rw [hd, ← FiniteSignal.indicator?_mapTime]
  cases FiniteSignal.indicator? obj.possiblyTrueSignal.duration lo hi true with
  | none => rfl
  | some ind =>
    simp only [Option.map_some, Option.bind_some]
    have hc := FiniteSignal.combine?_mapTime (· || ·) [obj.possiblyTrueSignal, ind]
    simp only [List.map_cons, List.map_nil] at hc
    rw [show (obj.mapTime toReal).possiblyTrueSignal =
      obj.possiblyTrueSignal.mapTime toReal from rfl, ← hc]
    cases FiniteSignal.combine? (· || ·) [obj.possiblyTrueSignal, ind] <;> rfl

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- Marking a float builder possibly false, read as reals, is the real marking. -/
theorem aux_setPossiblyFalse?_mapTime (obj : FiniteKleeneSignalBuilder T)
    (lo hi : T) : -- --- CONCL ---
    (obj.setPossiblyFalse? lo hi).map (FiniteKleeneSignalBuilder.mapTime toReal) =
      (obj.mapTime toReal).setPossiblyFalse? (toReal lo) (toReal hi) := by -- --- PROOF ---
  unfold FiniteKleeneSignalBuilder.setPossiblyFalse?
  dsimp only
  have hd : (obj.mapTime toReal).possiblyFalseSignal.duration =
      toReal obj.possiblyFalseSignal.duration :=
    FiniteSignal.duration_mapTime toReal toReal_zero_eq _
  rw [hd, ← FiniteSignal.indicator?_mapTime]
  cases FiniteSignal.indicator? obj.possiblyFalseSignal.duration lo hi true with
  | none => rfl
  | some ind =>
    simp only [Option.map_some, Option.bind_some]
    have hc := FiniteSignal.combine?_mapTime (· || ·) [obj.possiblyFalseSignal, ind]
    simp only [List.map_cons, List.map_nil] at hc
    rw [show (obj.mapTime toReal).possiblyFalseSignal =
      obj.possiblyFalseSignal.mapTime toReal from rfl, ← hc]
    cases FiniteSignal.combine? (· || ·) [obj.possiblyFalseSignal, ind] <;> rfl

omit [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)] in
/-- One proposition analyzed on a float analyzer, read as reals, is the real analysis. -/
theorem aux_analyzeKey_mapTime [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)]
    (obj : ReachSetAnalyzer T S n) (set : S n) (loc : ℕ) (lo hi : T)
    (p : String × AtomicProposition S n) : -- --- CONCL ---
    (obj.analyzeKey (𝕋 := 𝕋) set loc lo hi p).map (ReachSetAnalyzer.mapTime toReal) =
      (obj.mapTime toReal).analyzeKey (𝕋 := 𝕋) set loc (toReal lo) (toReal hi)
        p := by -- --- PROOF ---
  unfold ReachSetAnalyzer.analyzeKey
  rw [aux_maskOk_mapTime]
  have hl : (obj.mapTime toReal).sigBuilder.lookup p.1 =
      (obj.sigBuilder.lookup p.1).map (FiniteKleeneSignalBuilder.mapTime toReal) :=
    lookup_map_snd _ _ _
  rw [hl]
  cases obj.sigBuilder.lookup p.1 with
  | none => rfl
  | some b =>
    simp only [Option.map_some, Option.bind_some]
    by_cases hm : obj.maskOk p.1 lo hi = true
    · rw [if_pos hm, if_pos hm]
      -- the marking as possibly true
      have ht : (if p.2.canBeTrue (𝕋 := 𝕋) set loc then
          (b.mapTime toReal).setPossiblyTrue? (toReal lo) (toReal hi)
          else some (b.mapTime toReal)) = (if p.2.canBeTrue (𝕋 := 𝕋) set loc then
          b.setPossiblyTrue? lo hi else some b).map (FiniteKleeneSignalBuilder.mapTime toReal) := by
        split_ifs
        · exact (aux_setPossiblyTrue?_mapTime b lo hi).symm
        · rfl
      rw [ht]
      cases (if p.2.canBeTrue (𝕋 := 𝕋) set loc then b.setPossiblyTrue? lo hi else some b) with
      | none => rfl
      | some b1 =>
        simp only [Option.map_some, Option.bind_some]
        -- the marking as possibly false
        have hf : (if p.2.canBeFalse (𝕋 := 𝕋) set loc then
            (b1.mapTime toReal).setPossiblyFalse? (toReal lo) (toReal hi)
            else some (b1.mapTime toReal)) = (if p.2.canBeFalse (𝕋 := 𝕋) set loc then
            b1.setPossiblyFalse? lo hi else some b1).map
              (FiniteKleeneSignalBuilder.mapTime toReal) := by
          split_ifs
          · exact (aux_setPossiblyFalse?_mapTime b1 lo hi).symm
          · rfl
        rw [hf]
        cases (if p.2.canBeFalse (𝕋 := 𝕋) set loc then b1.setPossiblyFalse? lo hi
          else some b1) with
        | none => rfl
        | some b2 =>
          simp only [Option.map_some]
          unfold ReachSetAnalyzer.mapTime
          simp only
          rw [replaceKey_map_snd]
    · rw [if_neg hm, if_neg hm]
      rfl

/-- One time interval analyzed on a float analyzer, read as reals, is the real analysis. -/
theorem aux_analyzeTimeInterval_mapTime (obj : ReachSetAnalyzer T S n) (set : S n) (loc : ℕ)
    (lo hi : T) : -- --- CONCL ---
    (obj.analyzeTimeInterval (𝕋 := 𝕋) set loc lo hi).map (ReachSetAnalyzer.mapTime toReal) =
      (obj.mapTime toReal).analyzeTimeInterval (𝕋 := 𝕋) set loc (toReal lo)
        (toReal hi) := by -- --- PROOF ---
  unfold ReachSetAnalyzer.analyzeTimeInterval
  rw [foldlM_option_map _ (fun o p => o.analyzeKey (𝕋 := 𝕋) set loc (toReal lo) (toReal hi) p)
    (ReachSetAnalyzer.mapTime toReal) id
    (fun o p => aux_analyzeKey_mapTime o set loc lo hi p), List.map_id]
  rfl

/-- One reach set analyzed on a float analyzer, read as reals, is the real analysis of the reach
set read as reals. -/
theorem aux_analyzeSingle_mapTime (obj : ReachSetAnalyzer T S n)
    (R : ReachSetAnalyzer.Entry T S n) :
    (obj.analyzeSingle (𝕋 := 𝕋) R).map (ReachSetAnalyzer.mapTime toReal) =
      (obj.mapTime toReal).analyzeSingle (𝕋 := 𝕋) (R.mapTime toReal) := by
  unfold ReachSetAnalyzer.analyzeSingle
  exact foldlM_option_map _ _ _ _ (fun o t => aux_analyzeTimeInterval_mapTime o
    t.set R.loc t.time.inf t.time.sup) _ _

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- The signals of a float analyzer, read as reals, are those of the analyzer read as reals. -/
theorem aux_signals_mapTime (obj : ReachSetAnalyzer T S n) : -- --- CONCL ---
    obj.signals.map (List.map fun p => (p.1, p.2.mapTime toReal)) =
      (obj.mapTime toReal).signals := by -- --- PROOF ---
  unfold ReachSetAnalyzer.signals
  rw [mapM_option_map]
  congr 1
  funext p
  -- each proposition's builder is the float one read as reals
  have hl : (obj.mapTime toReal).sigBuilder.lookup p.1 =
      (obj.sigBuilder.lookup p.1).map (FiniteKleeneSignalBuilder.mapTime toReal) :=
    lookup_map_snd _ _ _
  rw [hl]
  cases obj.sigBuilder.lookup p.1 with
  | none => rfl
  | some b =>
    simp only [Option.map_some, Option.bind_some]
    -- and its three-valued signal the float one read as reals
    have hk : b.kleeneSignal?.map (FiniteSignal.mapTime toReal) =
        (b.mapTime toReal).kleeneSignal? := by
      unfold FiniteKleeneSignalBuilder.kleeneSignal?
      rw [FiniteSignal.combine?_mapTime]
      rfl
    rw [← hk]
    cases b.kleeneSignal? <;> rfl

omit [ExactLe T] [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- Mapping the time stamps keeps the parents, so the children of every entry. -/
theorem aux_children_mapTime (R : List (ReachSetAnalyzer.Entry T S n)) :
    ReachSetAnalyzer.children (R.map (ReachSetAnalyzer.Entry.mapTime toReal)) =
      ReachSetAnalyzer.children R := by
  funext parent
  unfold ReachSetAnalyzer.children
  simp only [List.length_map, List.getElem?_map, Option.map_map]
  rfl

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- A valid mask that lets an interval through lets every interval enclosing it through. -/
theorem aux_maskOk_mono (obj : ReachSetAnalyzer ℝ S n) (hm : ∀ p ∈ obj.masks, p.2.IsValid)
    (k : String) {lo hi lo' hi' : ℝ} (hlo : lo ≤ lo') (hhi : hi' ≤ hi) (hlh : lo' ≤ hi')
    (h0 : 0 ≤ hi') (h : obj.maskOk k lo' hi' = true) : -- --- CONCL ---
    obj.maskOk k lo hi = true := by -- --- PROOF ---
  unfold ReachSetAnalyzer.maskOk at h ⊢
  cases hk : obj.masks.lookup k with
  | none => rfl
  | some m =>
    rw [hk] at h
    have hmem : (k, m) ∈ obj.masks := by
      obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp hk
      rw [hl]; simp
    have hv := hm _ hmem
    -- a cell of value true meets the small interval, so the large one
    obtain ⟨-, -, h3⟩ := FiniteSignal.max_spec m hv lo' hi' hlh h0
    obtain ⟨-, h2', -⟩ := FiniteSignal.max_spec m hv lo hi (hlo.trans (hlh.trans hhi))
      (h0.trans hhi)
    rcases h3 with h3 | ⟨c, hc, hc1, hc2, hc3⟩
    · simp only at h ⊢
      rw [h3] at h
      exact absurd h (by decide)
    · have := h2' c hc (hlo.trans hc1) (hc2.trans hhi)
      simp only at h ⊢
      rw [hc3, h] at this
      cases hx : m.max lo hi
      · rw [hx] at this; exact absurd this (by decide)
      · rfl

omit [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)] in
/-- Signals sound for reach sets are sound for any whose time intervals those enclose. -/
theorem aux_signalsSound_of_hasEnclosingTimes (obj : ReachSetAnalyzer ℝ S n) (d : ℝ)
    (hm : ∀ p ∈ obj.masks, p.2.IsValid) (R Rx : List (ReachSetAnalyzer.Entry ℝ S n))
    (w : List ℕ) (out : List (String × FiniteSignal ℝ Kleene)) (hs : obj.SignalsSound d R w out)
    (hR : ReachSetAnalyzer.HasEnclosingTimes R Rx) : -- --- CONCL ---
    obj.SignalsSound d Rx w out := by -- --- PROOF ---
  intro k s hks ap hap
  obtain ⟨hv, hd, hts⟩ := hs k s hks ap hap
  refine ⟨hv, hd, fun t h0 h1 => ?_⟩
  obtain ⟨v, hat, htt, hff⟩ := hts t h0 h1
  -- an exact timed set is inside a float one, whose mask and cover then hold too
  have key : ∀ j ex, Rx[j - 1]? = some ex → ∀ stx ∈ ex.timeInterval,
      obj.maskOk k stx.time.inf stx.time.sup = true →
      FiniteKleeneSignalBuilder.Covers d t stx.time.inf stx.time.sup →
      ∃ e, R[j - 1]? = some e ∧ e.loc = ex.loc ∧ ∃ st ∈ e.timeInterval, st.set = stx.set ∧
        obj.maskOk k st.time.inf st.time.sup = true ∧
        FiniteKleeneSignalBuilder.Covers d t st.time.inf st.time.sup := by
    intro j ex hex stx hstx hmk hcov
    -- the enclosing entry at the same index, and its timed set around the exact one
    obtain ⟨e, he⟩ : ∃ e, R[j - 1]? = some e := by
      have hlt : j - 1 < Rx.length := (List.getElem?_eq_some_iff.mp hex).1
      exact ⟨_, List.getElem?_eq_getElem (hR.1 ▸ hlt)⟩
    obtain ⟨hloc, hsets⟩ := hR.2 (j - 1) e ex he hex
    obtain ⟨st, hst, hset, hlo, hhi⟩ := hsets stx hstx
    obtain ⟨c1, c2, c3, c4⟩ := hcov
    -- an interval that covers a time is proper
    have hlh : stx.time.inf ≤ stx.time.sup := by
      rcases c4 with c4 | c4
      · exact c3.trans c4.le
      · exact (c2.le).trans c4
    refine ⟨e, he, hloc.symm, st, hst, hset,
      aux_maskOk_mono obj hm k hlo hhi hlh c1.le hmk,
      ⟨c1.trans_le hhi, hlo.trans_lt c2, hlo.trans c3, ?_⟩⟩
    rcases c4 with c4 | c4
    · exact Or.inl (c4.trans_le hhi)
    · exact Or.inr (c4.trans hhi)
  -- a value on the enclosing intervals is one on the exact ones
  refine ⟨v, hat, fun hvt j hj ex hex stx hstx hmk hcov x hx => ?_,
    fun hvf j hj ex hex stx hstx hmk hcov x hx => ?_⟩
  · obtain ⟨e, he, hloc, st, hst, hset, hmk', hcov'⟩ := key j ex hex stx hstx hmk hcov
    rw [← hloc]
    exact htt hvt j hj e he st hst hmk' hcov' x (hset ▸ hx)
  · obtain ⟨e, he, hloc, st, hst, hset, hmk', hcov'⟩ := key j ex hex stx hstx hmk hcov
    rw [← hloc]
    exact hff hvf j hj e he st hst hmk' hcov' x (hset ▸ hx)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyze_sound_of_hasEnclosingTimes
    (aps : List (String × AtomicProposition S n)) (dur : T)
    (masks : List (String × FiniteSignal T Bool)) (hd : 0 ≤ toReal dur)
    (hnd : (aps.map Prod.fst).Nodup) (hm : ∀ p ∈ masks, (p.2.mapTime toReal).IsValid)
    (R : List (ReachSetAnalyzer.Entry T S n))
    (hR : ∀ e ∈ R, ∀ s ∈ e.timeInterval, toReal s.time.inf < toReal s.time.sup)
    (outs : List (List (String × FiniteSignal T Kleene))) : -- --- CONCL ---
    ∀ obj ∈ ReachSetAnalyzer.mk? aps dur masks,
      obj.analyze (𝕋 := 𝕋) R = some outs →
      ∀ out ∈ outs, ∃ w, ReachSetAnalyzer.Branch (ReachSetAnalyzer.children R) 0 w ∧
        ∀ Rx, ReachSetAnalyzer.HasEnclosingTimes
            (R.map (ReachSetAnalyzer.Entry.mapTime toReal)) Rx →
          (obj.mapTime toReal).SignalsSound (toReal dur) Rx w
            (out.map fun p => (p.1, p.2.mapTime toReal)) := by -- --- PROOF ---
  intro obj (hobj : ReachSetAnalyzer.mk? aps dur masks = some obj) h out hout
  -- the analyzer read as reals is the real constructor's
  have hobjR := aux_mk?_mapTime aps dur masks
  rw [hobj, Option.map_some] at hobjR
  obtain ⟨obj0, hmk, -, hmasks, hr⟩ := (ReachSetAnalyzer.mk?_spec aps (toReal dur)
    (masks.map fun p => (p.1, p.2.mapTime toReal))).2 hd hnd
  have hobj0 : obj.mapTime toReal = obj0 := Option.some.inj (hobjR.trans hmk)
  -- a branch of the float tree, and the float analyzer at its leaf
  obtain ⟨w, obj', hw, hf, hsig⟩ := ReachSetAnalyzer.analyzeTree_sound _ _ _ _ _ _ _ h out hout
  refine ⟨w, hw, fun Rx hRx => ?_⟩
  -- the same branch read as reals
  have hfR : w.foldlM (fun o j => ((R.map (ReachSetAnalyzer.Entry.mapTime toReal))[j - 1]?).bind
      fun e => o.analyzeSingle (𝕋 := 𝕋) e) (obj.mapTime toReal) =
      some (obj'.mapTime toReal) := by
    have := foldlM_option_map (fun o j => (R[j - 1]?).bind fun e => o.analyzeSingle (𝕋 := 𝕋) e)
      (fun o j => ((R.map (ReachSetAnalyzer.Entry.mapTime toReal))[j - 1]?).bind
        fun e => o.analyzeSingle (𝕋 := 𝕋) e) (ReachSetAnalyzer.mapTime toReal) id (fun o j => by
          simp only [id_eq, List.getElem?_map]
          cases R[j - 1]? with
          | none => rfl
          | some e => exact aux_analyzeSingle_mapTime o e) w obj
    rw [List.map_id, hf, Option.map_some] at this
    exact this.symm
  -- its signals read as reals
  have hsR : (obj'.mapTime toReal).signals =
      some (out.map fun p => (p.1, p.2.mapTime toReal)) := by
    rw [← aux_signals_mapTime, hsig, Option.map_some]
  -- the tree read as reals has proper intervals and the same branches
  have hRR : ∀ e ∈ R.map (ReachSetAnalyzer.Entry.mapTime toReal), ∀ s ∈ e.timeInterval,
      s.time.inf < s.time.sup := by
    intro e he s hs
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
    exact hR e0 he0 s0 hs0
  have hwR : ReachSetAnalyzer.Branch (ReachSetAnalyzer.children
      (R.map (ReachSetAnalyzer.Entry.mapTime toReal))) 0 w := by
    rw [aux_children_mapTime]; exact hw
  -- sound for the float intervals read as reals, so for the exact ones they enclose
  have hsound := ReachSetAnalyzer.signalsSound_of_branch (𝕋 := 𝕋) (obj.mapTime toReal)
    (toReal dur) (hobj0 ▸ hr) _ w (ReachSetAnalyzer.branch_proper _ hRR w hwR) _ hfR _ hsR
  -- the masks read as reals are valid
  have hmR : ∀ p ∈ (obj.mapTime toReal).masks, p.2.IsValid := by
    rw [hobj0, hmasks]
    intro p hp
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
    exact hm p0 hp0
  exact aux_signalsSound_of_hasEnclosingTimes _ _ hmR _ _ w _ hsound hRx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
