module

public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveSetCorrect
public import CORALean.Specification.Instances
public import CORALean.Specification.STLInterval.Theorems.ContainsZeroIff
public import CORALean.Specification.STLInterval.Theorems.IsequalZeroIff

@[expose] public section

/-!
# `observeSet_correct` fails when a time is observed twice

[1, Alg. 1] sets each atom's signal on the interval of every new reachable set, and [1, Alg. 2]
drops what a parent has decided. For `φ = F_[0,2] p`, a first observation with `p` false on
`[0,2]` makes the root `False` at `0` and erases `p` there; a second one with `p` unknown on `[1,2]`
finds `p` inconclusive at `0`, so the root keeps `False` while the satisfaction signal is unknown at
`0`. The hypothesis `hdisj` of `observeSet_correct` cannot be dropped. The paper's example, `p`
true on `[1,2]` and then false, is not a run of CORA's analyzer: the first observation propagates
`[0,2]` into `p`, and `OnlineAnalyzerNode.conflicts` refuses an observation from `1` on.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* with the atom `x₀ ∈ [-10, 0]` over boxes of `ℝ`, the conclusion of `observeSet_correct` fails for
  `F_[0,2] a` on the observations of `[1, 2]` on `[0,2]` and of `[-1, 1]` on `[1,2]`

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


open scoped CORALean.Float in
/-- The boxes `Interval (Vec ℝ k)` over `ℝ`, a set type the atoms are checked against. -/
abbrev OnlineReachSetAnalyzer.boxes : ℕ → Type := ℐ𝒱[ℝ]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section signals

/-- A real bound read as an extended real. -/
private theorem aux_toEReal (x : ℝ) :
    STLInterval.toEReal ((x : ℝ) : WithTop ℝ) = (x : EReal) := rfl

/-- The time interval `[0,2]` of the until. -/
private noncomputable def aux_I2 : STLInterval ℝ :=
  .nonempty 0 ((2 : ℝ) : WithTop ℝ) true true (by simp)
    (Or.inl (by rw [aux_toEReal, Float.toReal_real]; exact_mod_cast (by norm_num : (0 : ℝ) < 2)))
    (by simp [Float.toReal_real])

/-- The time interval `[1,2]` of the second observation. -/
private noncomputable def aux_J : STLInterval ℝ :=
  .nonempty 1 ((2 : ℝ) : WithTop ℝ) true true (by simp)
    (Or.inl (by rw [aux_toEReal, Float.toReal_real]; exact_mod_cast (by norm_num : (1 : ℝ) < 2)))
    (by simp [Float.toReal_real])

/-- A time lies in a closed interval iff it lies between the bounds. -/
private theorem aux_mem_cc (l u : ℝ) h1 h2 h3 (t : ℝ) :
    t ∈ (STLInterval.nonempty l ((u : ℝ) : WithTop ℝ) true true h1 h2 h3).set ↔
      l ≤ t ∧ t ≤ u := by
  simp only [STLInterval.set, STLInterval.rawSet, aux_toEReal, Float.toReal_real,
    Set.mem_setOf_eq, true_and]
  simp only [EReal.coe_lt_coe_iff, EReal.coe_eq_coe_iff, ← le_iff_lt_or_eq]

/-- The times of `[0,2]`. -/
private theorem aux_mem_I2 (t : ℝ) : t ∈ aux_I2.set ↔ 0 ≤ t ∧ t ≤ 2 := aux_mem_cc _ _ _ _ _ t

/-- The times of `[1,2]`. -/
private theorem aux_mem_J (t : ℝ) : t ∈ aux_J.set ↔ 1 ≤ t ∧ t ≤ 2 := aux_mem_cc _ _ _ _ _ t

/-- The interval `getAllProp` gives a node with propagated interval `C`. -/
private noncomputable def aux_A (C : STLInterval ℝ) : STLInterval ℝ :=
  STLInterval.stlInterval (0 : ℝ) (OnlineAnalyzerNode.propBound 0 [C] (⊤, true)).1 true
    (OnlineAnalyzerNode.propBound 0 [C] (⊤, true)).2 (by simp)

/-- The atom signal after the first observation: `False` on `[0,2]`, inconclusive elsewhere. -/
private noncomputable def aux_P1 : FourValuedSignal ℝ :=
  (FourValuedSignal.uniformSignal .ii).set aux_I2 (FourValued.fromKleene .ff)

/-- The until is inconclusive where one refinement has a witness and the other none. -/
private theorem aux_until_ii (l r s : FourValuedSignal ℝ) (hl : l.IsValid) (hr : r.IsValid)
    (U : STLInterval ℝ) (hs : l.until U r = some s) (t : ℝ) (ht : 0 ≤ t)
    (hmax : ∃ t', t' - t ∈ U.set ∧ (r.at t' = .tt ∨ r.at t' = .ii) ∧
      ∀ x, t < x → x < t' → l.at x = .tt ∨ l.at x = .ii)
    (hmin : ¬ ∃ t', t' - t ∈ U.set ∧ r.at t' = .tt ∧ ∀ x, t < x → x < t' → l.at x = .tt)
    : -- --- CONCL ---
    s.at t = .ii := by -- --- PROOF ---
  obtain ⟨s', hs', -, h⟩ := FourValuedSignal.until_spec l r hl hr U
  rw [hs] at hs'; cases hs'
  -- the witnesses lie at times `≥ 0`, where the refinements are read off the signals
  have hpos : ∀ t', t' - t ∈ U.set → 0 ≤ t' := fun t' hu => by
    have := STLInterval.zero_le_of_mem_set U _ hu; linarith
  have hat := fun x (hx0 : 0 ≤ x) => l.toKleeneSignal_at_iff hl x hx0
  have hat' := fun x (hx0 : 0 ≤ x) => r.toKleeneSignal_at_iff hr x hx0
  obtain ⟨-, hm⟩ := KleeneSignal.until_spec _ _ (l.toKleeneSignal_spec hl Kleene.ff).1
    (r.toKleeneSignal_spec hr Kleene.ff).1 U
  obtain ⟨-, hx⟩ := KleeneSignal.until_spec _ _ (l.toKleeneSignal_spec hl Kleene.tt).1
    (r.toKleeneSignal_spec hr Kleene.tt).1 U
  -- the refinement with inconclusive as `True` has the witness
  have hmax' : ((l.toKleeneSignal Kleene.tt).until U (r.toKleeneSignal Kleene.tt)).at t =
      Kleene.tt := by
    refine ((hx t ht).1).2 ?_
    obtain ⟨t', hu, hr', hl'⟩ := hmax
    exact ⟨t', hu, (hat' t' (hpos t' hu)).2.2.2.1.2 hr',
      fun x h1 h2 => (hat x (by linarith)).2.2.2.1.2 (hl' x h1 h2)⟩
  -- the other has none
  have hmin' : ((l.toKleeneSignal Kleene.ff).until U (r.toKleeneSignal Kleene.ff)).at t ≠
      Kleene.tt := by
    intro h
    obtain ⟨t', hu, hr', hl'⟩ := ((hm t ht).1).1 h
    exact hmin ⟨t', hu, (hat' t' (hpos t' hu)).1.1 hr',
      fun x h1 h2 => (hat x (by linarith)).1.1 (hl' x h1 h2)⟩
  exact ((h t ht).1.2 (by rw [hmax']; exact hmin'))

/-- The first atom signal is valid, `False` on `[0,2]` and inconclusive elsewhere. -/
private theorem aux_P1_spec : aux_P1.IsValid ∧ ∀ x : ℝ, 0 ≤ x →
    (x ∈ aux_I2.set → aux_P1.at x = .ff) ∧ (x ∉ aux_I2.set → aux_P1.at x = .ii) := by
  obtain ⟨hv, hat⟩ := FourValuedSignal.uniformSignal_spec FourValued.ii
  obtain ⟨hv1, h1⟩ := FourValuedSignal.set_spec _ hv aux_I2 (FourValued.fromKleene .ff)
  exact ⟨hv1, fun x hx => ⟨fun hm => (h1 x hx).1 hm, fun hm => by
    unfold aux_P1; rw [(h1 x hx).2 hm, hat x hx]⟩⟩

/-- The until after the first observation: `False` at `0`, inconclusive at `1 / 2`. -/
private theorem aux_one : -- --- CONCL ---
    ∃ Δ, (FourValuedSignal.uniformSignal .tt).until aux_I2 aux_P1 = some Δ ∧
      Δ.IsValid ∧ Δ.at 0 = .ff ∧ Δ.at (1 / 2) = .ii := by -- --- PROOF ---
  obtain ⟨hP, hPat⟩ := aux_P1_spec
  obtain ⟨hT, hTat⟩ := FourValuedSignal.uniformSignal_spec FourValued.tt
  obtain ⟨Δ, hΔ, hΔv, h⟩ := FourValuedSignal.until_spec _ _ hT hP aux_I2
  refine ⟨Δ, hΔ, hΔv, ?_, ?_⟩
  · -- `p` is false on all of `[0,2]`
    refine (h 0 le_rfl).2.2.2.2 fun t' ht' => Or.inl ?_
    rw [sub_zero] at ht'
    exact (hPat t' ((aux_mem_I2 t').1 ht').1).1 ht'
  · -- at `1 / 2` the window reaches `5 / 2`, where `p` is inconclusive, and never meets `True`
    refine aux_until_ii _ _ Δ hT hP aux_I2 hΔ (1 / 2) (by norm_num) ⟨5 / 2, ?_, Or.inr ?_, ?_⟩ ?_
    · rw [aux_mem_I2]; norm_num
    · exact (hPat (5 / 2) (by norm_num)).2 (by rw [aux_mem_I2]; norm_num)
    · exact fun x h1 _ => Or.inl (hTat x (by linarith))
    · rintro ⟨t', hu, hr, -⟩
      obtain ⟨hu1, hu2⟩ := (aux_mem_I2 _).1 hu
      by_cases hm : t' ∈ aux_I2.set
      · rw [(hPat t' (by linarith)).1 hm] at hr; exact absurd hr (by simp)
      · rw [(hPat t' (by linarith)).2 hm] at hr; exact absurd hr (by simp)

/-- A conclusive prefix `C` holding `0` and not `1 / 2` conflicts with nothing from `1` on. -/
private theorem aux_prefix (C : STLInterval ℝ) (h0 : (0 : ℝ) ∈ C.set) (hh : (1 / 2 : ℝ) ∉ C.set)
    : -- --- CONCL ---
    OnlineAnalyzerNode.conflicts 0 aux_J.infimum.value aux_J.infimum.closed [C] = some false ∧
      (0 : ℝ) ∈ (aux_A C).set := by -- --- PROOF ---
  cases C with
  | empty => simp [STLInterval.set] at h0
  | nonempty l u lc rc b c z =>
    simp only [STLInterval.set, STLInterval.rawSet, Float.toReal_real, Set.mem_setOf_eq] at h0 hh
    -- the lower bound is `0`, so `1 / 2` is out only by the upper bound
    have hl0 : l = 0 := by
      refine le_antisymm ?_ (by simpa using z)
      rcases h0.1 with h | ⟨-, h⟩
      · exact_mod_cast h.le
      · exact_mod_cast h.le
    subst hl0
    have hlt : ((0 : ℝ) : EReal) < ((1 / 2 : ℝ) : EReal) := by exact_mod_cast (by norm_num)
    have hu : STLInterval.toEReal u ≤ ((1 / 2 : ℝ) : EReal) := by
      by_contra hcon
      exact hh ⟨Or.inl (by simp), Or.inl (not_le.1 hcon)⟩
    have hu1 : STLInterval.toEReal u < ((1 : ℝ) : EReal) :=
      hu.trans_lt (by exact_mod_cast (by norm_num))
    have hlt1 : STLInterval.toEReal u < ⊤ := hu1.trans (EReal.coe_lt_top _)
    refine ⟨?_, ?_⟩
    · -- the bound is below the start `1` of the new observation
      simp only [OnlineAnalyzerNode.conflicts, STLInterval.supremum, aux_J, STLInterval.infimum,
        aux_toEReal, STLInterval.withinTol_zero]
      rw [if_neg]
      rintro (h | ⟨h, -⟩)
      · exact absurd h (not_lt.2 hu1.le)
      · exact absurd h hu1.ne
    · -- the erased interval keeps the prefix, and so `0`
      unfold aux_A
      have hb : OnlineAnalyzerNode.propBound 0 [STLInterval.nonempty 0 u lc rc b c z]
          ((⊤ : WithTop ℝ), true) = (u, rc) := by
        simp only [OnlineAnalyzerNode.propBound]
        rw [if_pos (Or.inl (by simpa [STLInterval.toEReal] using hlt1))]
      simp only [hb]
      rw [STLInterval.set_stlInterval]
      simp only [STLInterval.rawSet, Set.mem_setOf_eq, Float.toReal_real]
      exact ⟨by simp, h0.2⟩

/-- The root after the first observation is `False` at `0` and conclusive only near `0`. -/
private theorem aux_R1 (Δ : FourValuedSignal ℝ) (hv : Δ.IsValid) (h0 : Δ.at 0 = .ff)
    (h2 : Δ.at (1 / 2) = .ii) : -- --- CONCL ---
    let R := (FourValuedSignal.uniformSignal .ii).merge Δ
    R.IsValid ∧ R.at 0 = .ff ∧ (0 : ℝ) ∈ (R.conclusiveInterval .empty).set ∧
      (1 / 2 : ℝ) ∉ (R.conclusiveInterval .empty).set := by -- --- PROOF ---
  intro R
  obtain ⟨hU, hUat⟩ := FourValuedSignal.uniformSignal_spec FourValued.ii
  obtain ⟨hR, h⟩ := FourValuedSignal.merge_spec _ Δ hU hv
  have hR0 : ((FourValuedSignal.uniformSignal .ii).merge Δ).at 0 = .ff :=
    ((h 0 le_rfl).1 (by rw [h0]; simp)).trans h0
  have hR2 : ((FourValuedSignal.uniformSignal .ii).merge Δ).at (1 / 2) = .ii :=
    ((h (1 / 2) (by norm_num)).2 h2).trans (hUat _ (by norm_num))
  refine ⟨hR, hR0, ?_, ?_⟩
  · -- the root is conclusive at `0`
    rw [FourValuedSignal.conclusiveInterval_spec _ hR]
    refine ⟨le_rfl, fun x hx1 hx2 => Or.inr ?_⟩
    rw [le_antisymm hx2 hx1, hR0]; simp
  · -- and inconclusive at `1 / 2`
    rw [FourValuedSignal.conclusiveInterval_spec _ hR]
    rintro ⟨-, hall⟩
    rcases hall (1 / 2) (by norm_num) (by norm_num) with h | h
    · simp [STLInterval.set_empty] at h
    · exact h hR2

/-- Nothing propagated yet is never larger than what is propagated. -/
private theorem aux_hs_empty (C : STLInterval ℝ) : -- --- CONCL ---
    ¬ (¬ STLInterval.isequal 0 (STLInterval.empty : STLInterval ℝ) C ∧
      STLInterval.contains_ 0 (STLInterval.empty : STLInterval ℝ) C) := by -- --- PROOF ---
  rintro ⟨h1, h2⟩
  apply h1
  rw [STLInterval.isequal_zero_iff, STLInterval.set_empty]
  rw [STLInterval.contains_zero_iff, STLInterval.set_empty] at h2
  exact (Set.subset_empty_iff.1 h2).symm

/-- A propagated interval that grows is not smaller than before. -/
private theorem aux_hs_sub (C C' : STLInterval ℝ) (h : C.set ⊆ C'.set) :
    ¬ (¬ STLInterval.isequal 0 C C' ∧ STLInterval.contains_ 0 C C') := by
  rintro ⟨h1, h2⟩
  rw [STLInterval.contains_zero_iff] at h2
  exact h1 ((STLInterval.isequal_zero_iff _ _).2 (Set.Subset.antisymm h h2))

/-- The second observation leaves the root `False` at `0`, as the atom is inconclusive there. -/
private theorem aux_two (R1 : FourValuedSignal ℝ) (hR : R1.IsValid) (hR0 : R1.at 0 = .ff)
    (A : STLInterval ℝ) (hA : (0 : ℝ) ∈ A.set) : -- --- CONCL ---
    ∃ Δ, ((FourValuedSignal.uniformSignal .tt).set A .ii).until aux_I2
        ((aux_P1.set A .ii).set aux_J (FourValued.fromKleene .uu)) = some Δ ∧
      (R1.merge Δ).at 0 = .ff ∧
      (R1.conclusiveInterval .empty).set ⊆
        ((R1.merge Δ).conclusiveInterval .empty).set := by -- --- PROOF ---
  obtain ⟨hT, hTat⟩ := FourValuedSignal.uniformSignal_spec FourValued.tt
  obtain ⟨hP, hPat⟩ := aux_P1_spec
  obtain ⟨hT1, hT1at⟩ := FourValuedSignal.set_spec _ hT A FourValued.ii
  obtain ⟨hQ, hQat⟩ := FourValuedSignal.set_spec _ hP A FourValued.ii
  obtain ⟨hP2, hP2at⟩ := FourValuedSignal.set_spec _ hQ aux_J (FourValued.fromKleene .uu)
  obtain ⟨Δ, hΔ, hΔv, -⟩ := FourValuedSignal.until_spec _ _ hT1 hP2 aux_I2
  -- the atom is never `True`
  have hnt : ∀ x : ℝ, 0 ≤ x →
      ((aux_P1.set A .ii).set aux_J (FourValued.fromKleene .uu)).at x ≠ .tt := by
    intro x hx
    by_cases h1 : x ∈ aux_J.set
    · rw [(hP2at x hx).1 h1]; simp [FourValued.fromKleene]
    · rw [(hP2at x hx).2 h1]
      by_cases h2 : x ∈ A.set
      · rw [(hQat x hx).1 h2]; simp
      · rw [(hQat x hx).2 h2]
        by_cases h3 : x ∈ aux_I2.set
        · rw [(hPat x hx).1 h3]; simp
        · rw [(hPat x hx).2 h3]; simp
  -- and inconclusive at `0`, where the first observation was erased
  have h0 : ((aux_P1.set A .ii).set aux_J (FourValued.fromKleene .uu)).at 0 = .ii := by
    rw [(hP2at 0 le_rfl).2 (by rw [aux_mem_J]; norm_num), (hQat 0 le_rfl).1 hA]
  -- so the until is inconclusive at `0`: the witness `0` of the atom is only possible
  have hΔ0 : Δ.at 0 = .ii := by
    refine aux_until_ii _ _ Δ hT1 hP2 aux_I2 hΔ 0 le_rfl ⟨0, ?_, Or.inr h0, ?_⟩ ?_
    · rw [sub_zero, aux_mem_I2]; norm_num
    · intro x h1 h2; exact absurd h2 (not_lt.2 h1.le)
    · rintro ⟨t', hu, hr, -⟩
      rw [sub_zero] at hu
      exact hnt t' ((aux_mem_I2 t').1 hu).1 hr
  -- the merge keeps the root where the until is inconclusive, and the root only gains
  obtain ⟨hM, hMat⟩ := FourValuedSignal.merge_spec R1 Δ hR hΔv
  refine ⟨Δ, hΔ, ((hMat 0 le_rfl).2 hΔ0).trans hR0, fun t ht => ?_⟩
  rw [FourValuedSignal.conclusiveInterval_spec _ hR] at ht
  rw [FourValuedSignal.conclusiveInterval_spec _ hM]
  refine ⟨ht.1, fun x hx1 hx2 => ?_⟩
  rcases ht.2 x hx1 hx2 with h | h
  · exact Or.inl h
  · by_cases hd : Δ.at x = .ii
    · exact Or.inr (by rw [(hMat x hx1).2 hd]; exact h)
    · exact Or.inr (by rw [(hMat x hx1).1 hd]; exact hd)

end signals


section nodes

variable {S : ℕ → Type} {d : ℕ}

/-- The root node `F_[0,2] p` with signal `rs`. -/
private noncomputable def aux_root (rs : FourValuedSignal ℝ) :
    OnlineAnalyzerNode ℝ (AtomicProposition S d) :=
  { kind := .until, signal := rs, prop := [STLInterval.empty], dropPropagated := true, idx := 1,
    parents := [0], children := [2, 3], interval := some aux_I2, ap := none, tentative := none }

/-- The node of `true`, propagated up to `C`. -/
private noncomputable def aux_tt (ts : FourValuedSignal ℝ) (C : STLInterval ℝ) :
    OnlineAnalyzerNode ℝ (AtomicProposition S d) :=
  { kind := .true, signal := ts, prop := [C], dropPropagated := true, idx := 2, parents := [1],
    children := [], interval := none, ap := none, tentative := none }

/-- The node of the atom `a`, propagated up to `C`. -/
private noncomputable def aux_p (a : AtomicProposition S d) (ps : FourValuedSignal ℝ)
    (C : STLInterval ℝ) : OnlineAnalyzerNode ℝ (AtomicProposition S d) :=
  { kind := .ap, signal := ps, prop := [C], dropPropagated := true, idx := 3, parents := [1],
    children := [], interval := none, ap := some a,
    tentative := some TentativeKleeneSignal.emptySignal }

/-- The analyzer of `F_[0,2] a` with the given signals, propagated interval and counter. -/
private noncomputable def aux_st (a : AtomicProposition S d) (rs ts ps : FourValuedSignal ℝ)
    (C : STLInterval ℝ) (n : ℕ) (pr : List Bool) : OnlineReachSetAnalyzer ℝ S d :=
  { propagationFrequency := 1, nodes := [aux_root rs, aux_tt ts C, aux_p a ps C],
    leaves := [2, 3], numObservations := n, propagated := pr }

/-- The analyzer of `F_[0,2] a` before any observation. -/
private noncomputable def aux_obj0 (a : AtomicProposition S d) : OnlineReachSetAnalyzer ℝ S d :=
  aux_st a (OnlineAnalyzerNode.initSignal .until) (OnlineAnalyzerNode.initSignal .true)
    (OnlineAnalyzerNode.initSignal .ap) .empty 0 [false, false, false]

/-- Parsing `F_[0,2] a` gives the analyzer before any observation. -/
private theorem aux_mk (a : AtomicProposition S d) : -- --- CONCL ---
    OnlineReachSetAnalyzer.mk? (𝕋 := ℝ)
      (.until aux_I2 .tt (.ap "p" a) : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
      1 true = some (aux_obj0 a) := by -- --- PROOF ---
  -- the parser makes the until, then its two operands, with no cache hit
  simp [OnlineReachSetAnalyzer.mk?, OnlineReachSetAnalyzer.parse,
    OnlineReachSetAnalyzer.parseNew, OnlineAnalyzerNode.mk?, OnlineReachSetAnalyzer.Formula.kind,
    OnlineReachSetAnalyzer.Formula.key, OnlineReachSetAnalyzer.Formula.interval?,
    OnlineReachSetAnalyzer.Formula.ap?, OnlineReachSetAnalyzer.updateNode, aux_obj0, aux_st,
    aux_root, aux_tt, aux_p, OnlineAnalyzerNode.addChild, OnlineReachSetAnalyzer.Formula.keyEqv]
  rfl

/-- Propagating a growing interval to the node of `true` erases it from its signal. -/
private theorem aux_setPropagated_tt (ts : FourValuedSignal ℝ) (C C' : STLInterval ℝ)
    (hs : ¬ (¬ STLInterval.isequal 0 C C' ∧ STLInterval.contains_ 0 C C')) :
    (aux_tt (S := S) (d := d) ts C).setPropagated 0 1 C' =
      some (aux_tt (ts.set (aux_A C') .ii) C') := by
  simp [OnlineAnalyzerNode.setPropagated, aux_tt, hs, aux_A, OnlineAnalyzerNode.getAllProp]

/-- Propagating a growing interval to the atom node erases it from its signal. -/
private theorem aux_setPropagated_p (a : AtomicProposition S d) (ps : FourValuedSignal ℝ)
    (C C' : STLInterval ℝ)
    (hs : ¬ (¬ STLInterval.isequal 0 C C' ∧ STLInterval.contains_ 0 C C')) :
    (aux_p a ps C).setPropagated 0 1 C' = some (aux_p a (ps.set (aux_A C') .ii) C') := by
  simp [OnlineAnalyzerNode.setPropagated, aux_p, hs, aux_A, OnlineAnalyzerNode.getAllProp]

/-- The root is an until node. -/
@[simp] private theorem aux_root_kind (rs : FourValuedSignal ℝ) :
    (aux_root (S := S) (d := d) rs).kind = .until := rfl

/-- The root carries the interval `[0,2]`. -/
@[simp] private theorem aux_root_interval (rs : FourValuedSignal ℝ) :
    (aux_root (S := S) (d := d) rs).interval = some aux_I2 := rfl

/-- The signal of the root. -/
@[simp] private theorem aux_root_signal (rs : FourValuedSignal ℝ) :
    (aux_root (S := S) (d := d) rs).signal = rs := rfl

/-- The root has index `1`. -/
@[simp] private theorem aux_root_idx (rs : FourValuedSignal ℝ) :
    (aux_root (S := S) (d := d) rs).idx = 1 := rfl

/-- The signal of the node of `true`. -/
@[simp] private theorem aux_tt_signal (ts : FourValuedSignal ℝ) (C : STLInterval ℝ) :
    (aux_tt (S := S) (d := d) ts C).signal = ts := rfl

/-- The signal of the atom node. -/
@[simp] private theorem aux_p_signal (a : AtomicProposition S d) (ps : FourValuedSignal ℝ)
    (C : STLInterval ℝ) : (aux_p a ps C).signal = ps := rfl

/-- Nothing is propagated to the root. -/
@[simp] private theorem aux_root_prop (rs : FourValuedSignal ℝ) :
    (aux_root (S := S) (d := d) rs).prop = [STLInterval.empty] := rfl

/-- The children of the root. -/
@[simp] private theorem aux_root_children (rs : FourValuedSignal ℝ) :
    (aux_root (S := S) (d := d) rs).children = [2, 3] := rfl

/-- The node of `true` has no children. -/
@[simp] private theorem aux_tt_children (ts : FourValuedSignal ℝ) (C : STLInterval ℝ) :
    (aux_tt (S := S) (d := d) ts C).children = [] := rfl

/-- The atom node has no children. -/
@[simp] private theorem aux_p_children (a : AtomicProposition S d) (ps : FourValuedSignal ℝ)
    (C : STLInterval ℝ) : (aux_p a ps C).children = [] := rfl

/-- The node of `true` propagates unchanged. -/
private theorem aux_prop_tt (ts : FourValuedSignal ℝ) (C : STLInterval ℝ) :
    (aux_tt (S := S) (d := d) ts C).propagate 0 [] .empty = some (aux_tt ts C, []) := by
  simp [OnlineAnalyzerNode.propagate, aux_tt]

/-- The atom node propagates unchanged. -/
private theorem aux_prop_p (a : AtomicProposition S d) (ps : FourValuedSignal ℝ)
    (C : STLInterval ℝ) :
    (aux_p a ps C).propagate 0 [] .empty = some (aux_p a ps C, []) := by
  simp [OnlineAnalyzerNode.propagate, aux_p]

/-- A node with nothing propagated yet has the empty interval as `getAllProp`. -/
private theorem aux_getAllProp_empty (n : OnlineAnalyzerNode ℝ (AtomicProposition S d))
    (h : n.prop = [STLInterval.empty]) : OnlineAnalyzerNode.getAllProp 0 n = .empty := by
  simp [OnlineAnalyzerNode.getAllProp, h, OnlineAnalyzerNode.propBound, STLInterval.stlInterval]

/-- The root merges the until of its children and erases them up to the conclusive interval. -/
private theorem aux_prop_root (a : AtomicProposition S d) (rs ts ps : FourValuedSignal ℝ)
    (C : STLInterval ℝ) (Δ : FourValuedSignal ℝ) (hΔ : ts.until aux_I2 ps = some Δ)
    (C' : STLInterval ℝ) (hC' : C' = (rs.merge Δ).conclusiveInterval .empty)
    (hs : ¬ (¬ STLInterval.isequal 0 C C' ∧ STLInterval.contains_ 0 C C')) : -- --- CONCL ---
    (aux_root (S := S) (d := d) rs).propagate 0 [aux_tt ts C, aux_p a ps C] .empty =
      some (aux_root (rs.merge Δ), [aux_tt (ts.set (aux_A C') .ii) C',
        aux_p a (ps.set (aux_A C') .ii) C']) := by -- --- PROOF ---
  simp [OnlineAnalyzerNode.propagate, OnlineAnalyzerNode.combine, hΔ,
    aux_setPropagated_tt ts C C' hs, aux_setPropagated_p a ps C C' hs, aux_getAllProp_empty,
    ← hC']
  rfl

/-- The sorted children of the root. -/
private theorem aux_sort : ([2, 3].eraseDups.mergeSort fun a b ↦ decide (a ≤ b)) = [2, 3] := by
  rw [show [2, 3].eraseDups = [2, 3] from by rfl]
  exact List.mergeSort_eq_self _ (by simp)

/-- Propagation merges the until into the root and erases the children. -/
private theorem aux_propagate (a : AtomicProposition S d) (rs ts ps : FourValuedSignal ℝ)
    (C : STLInterval ℝ) (n : ℕ) (pr : List Bool) (Δ : FourValuedSignal ℝ)
    (hΔ : ts.until aux_I2 ps = some Δ) (C' : STLInterval ℝ)
    (hC' : C' = (rs.merge Δ).conclusiveInterval .empty)
    (hs : ¬ (¬ STLInterval.isequal 0 C C' ∧ STLInterval.contains_ 0 C C')) : -- --- CONCL ---
    OnlineReachSetAnalyzer.propagate 0 (aux_st a rs ts ps C n pr) .empty =
      some (aux_st a (rs.merge Δ) (ts.set (aux_A C') .ii) (ps.set (aux_A C') .ii) C' n
        [true, true, true]) := by -- --- PROOF ---
  -- the leaves are visited first, then the root
  simp [OnlineReachSetAnalyzer.propagate, aux_st, OnlineReachSetAnalyzer.propagateRec,
    aux_sort, List.foldlM_cons, aux_prop_tt, aux_prop_p, aux_prop_root a rs ts ps C Δ hΔ C' hC' hs]

end nodes


section main

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]

/-- One observation of an atom value on a nonempty interval, then the propagation. -/
private theorem aux_step (a : AtomicProposition S d) (s : S d) (v : Kleene)
    (hv : OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a s 0 = some v) (I : STLInterval ℝ)
    (hI : I ≠ .empty) (rs ts ps : FourValuedSignal ℝ) (C : STLInterval ℝ) (n : ℕ)
    (pr : List Bool)
    (hc : OnlineAnalyzerNode.conflicts 0 I.infimum.value I.infimum.closed [C] = some false)
    (Δ : FourValuedSignal ℝ) (hΔ : ts.until aux_I2 (ps.set I (FourValued.fromKleene v)) = some Δ)
    (C' : STLInterval ℝ) (hC' : C' = (rs.merge Δ).conclusiveInterval .empty)
    (hs : ¬ (¬ STLInterval.isequal 0 C C' ∧ STLInterval.contains_ 0 C C')) : -- --- CONCL ---
    OnlineReachSetAnalyzer.observeSet (𝕋 := 𝕋) 0 (aux_st a rs ts ps C n pr) s I 0 =
      some (aux_st a (rs.merge Δ) (ts.set (aux_A C') .ii)
        ((ps.set I (FourValued.fromKleene v)).set (aux_A C') .ii) C' (n + 1)
        [true, true, true]) := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc b c z =>
  -- both leaves accept the observation, the atom writes its value, then the root propagates
  simp [OnlineReachSetAnalyzer.observeSet, aux_st, OnlineReachSetAnalyzer.updateNode,
    aux_root, aux_tt, aux_p, OnlineAnalyzerNode.observeSet, hc, hv, Nat.mod_one]
  exact aux_propagate a rs ts _ C (n + 1) pr Δ hΔ C' hC' hs

/-- The satisfaction signal of the two observations is not `False` at `0`. -/
private theorem aux_sat (a : AtomicProposition S d) (s₁ s₂ : S d)
    (h₁ : OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a s₁ 0 = some .ff)
    (h₂ : OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a s₂ 0 = some .uu) (s : FourValuedSignal ℝ)
    (hs : (OnlineReachSetAnalyzer.Formula.until aux_I2 .tt (.ap "p" a) :
        OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)).sat
      (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) (fun _ => FourValuedSignal.uniformSignal .ii)
        [(s₁, aux_I2, 0), (s₂, aux_J, 0)]) = some s) : -- --- CONCL ---
    s.at 0 ≠ .ff := by -- --- PROOF ---
  -- the atom is `False` on `[0,2]`, then unknown on `[1,2]`, the later observation winning
  simp only [OnlineReachSetAnalyzer.Formula.sat, OnlineReachSetAnalyzer.observeAtoms,
    List.foldl_cons, List.foldl_nil, h₁, h₂, Option.bind_some] at hs
  obtain ⟨hT, hTat⟩ := FourValuedSignal.uniformSignal_spec FourValued.tt
  obtain ⟨hP, -⟩ := aux_P1_spec
  obtain ⟨hP2, hP2at⟩ := FourValuedSignal.set_spec _ hP aux_J (FourValued.fromKleene .uu)
  obtain ⟨s', hs', -, h⟩ := FourValuedSignal.until_spec _ _ hT hP2 aux_I2
  have hs'' : s' = s := by
    have := hs.symm.trans hs'
    exact (Option.some.inj this).symm
  subst hs''
  -- `False` at `0` would need the atom `False` at `1`, where it is unknown
  intro hff
  have := ((h 0 le_rfl).2.2.2.1 hff) 1 (by rw [sub_zero, aux_mem_I2]; norm_num)
  rcases this with h1 | ⟨x, hx1, hx2, hx⟩
  · rw [(hP2at 1 zero_le_one).1 (by rw [aux_mem_J]; norm_num)] at h1
    exact absurd h1 (by simp [FourValued.fromKleene])
  · rw [hTat x hx1.le] at hx; exact absurd hx (by simp)


/-- Over any set type with an atom `false` on one set and unknown on another, the conclusion of
`observeSet_correct` fails without `hdisj`. -/
private theorem aux_counterexample (a : AtomicProposition S d)
    (s₁ s₂ : S d) (h₁ : Kleene.ff ∈ OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a s₁ 0)
    (h₂ : Kleene.uu ∈ OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a s₂ 0) : -- --- CONCL ---
    ¬ ∀ φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d),
      (∀ l x y, (OnlineReachSetAnalyzer.Formula.ap l x).IsSub φ →
        (OnlineReachSetAnalyzer.Formula.ap l y).IsSub φ → x = y) →
      ∀ (dp : Bool) (obs : List (S d × STLInterval ℝ × ℕ)), obs ≠ [] →
        (∀ o ∈ obs, o.2.1 ≠ .empty) →
      ∀ obj₀ ∈ OnlineReachSetAnalyzer.mk? φ 1 dp,
        ∀ obj ∈ obs.foldlM (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) obj₀,
        ∃ s, φ.sat (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋)
            (fun _ => FourValuedSignal.uniformSignal .ii) obs) = some s ∧
          ∃ root, obj.nodes[0]? = some root ∧ ∀ t : ℝ, 0 ≤ t → root.signal.at t = s.at t
    := by -- --- PROOF ---
  intro H
  have h₁' := Option.mem_def.1 h₁
  have h₂' := Option.mem_def.1 h₂
  -- the first observation, and the root it decides at time `0`
  obtain ⟨Δ₁, hΔ₁, hΔ₁v, hΔ₁0, hΔ₁2⟩ := aux_one
  obtain ⟨hR₁, hR₁0, hC₀, hCh⟩ := aux_R1 Δ₁ hΔ₁v hΔ₁0 hΔ₁2
  set C₁ := ((FourValuedSignal.uniformSignal .ii).merge Δ₁).conclusiveInterval .empty with hC₁
  obtain ⟨hconf, hA⟩ := aux_prefix _ hC₀ hCh
  -- the second observation leaves the root where it was
  obtain ⟨Δ₂, hΔ₂, hR₂0, hsub⟩ := aux_two _ hR₁ hR₁0 _ hA
  have hne₁ : (aux_I2 : STLInterval ℝ) ≠ .empty := by simp [aux_I2]
  have hne₂ : (aux_J : STLInterval ℝ) ≠ .empty := by simp [aux_J]
  have hc₀ : OnlineAnalyzerNode.conflicts 0 aux_I2.infimum.value aux_I2.infimum.closed
      [STLInterval.empty] = some false := by
    simp [OnlineAnalyzerNode.conflicts, STLInterval.supremum]
  have hstep₁ := aux_step (𝕋 := 𝕋) a s₁ .ff h₁' aux_I2 hne₁ (OnlineAnalyzerNode.initSignal .until)
    (OnlineAnalyzerNode.initSignal .true) (OnlineAnalyzerNode.initSignal .ap) .empty 0
    [false, false, false] hc₀ Δ₁ hΔ₁ C₁ rfl (aux_hs_empty _)
  have hstep₂ := aux_step (𝕋 := 𝕋) a s₂ .uu h₂' aux_J hne₂
    ((OnlineAnalyzerNode.initSignal .until).merge Δ₁)
    ((OnlineAnalyzerNode.initSignal .true).set (aux_A C₁) .ii)
    (((OnlineAnalyzerNode.initSignal .ap).set aux_I2 (FourValued.fromKleene .ff)).set
      (aux_A C₁) .ii) C₁ (0 + 1) [true, true, true] hconf Δ₂ hΔ₂ _ rfl (aux_hs_sub _ _ hsub)
  -- the run of the two observations from the analyzer of `F_[0,2] p`
  obtain ⟨obj₂, hrun, hroot⟩ : ∃ obj₂ : OnlineReachSetAnalyzer ℝ S d,
      [(s₁, aux_I2, 0), (s₂, aux_J, 0)].foldlM
        (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) (aux_obj0 a) = some obj₂ ∧
      obj₂.nodes[0]? = some (aux_root (((FourValuedSignal.uniformSignal .ii).merge Δ₁).merge Δ₂))
      := by
    simp only [List.foldlM_cons, List.foldlM_nil]
    unfold aux_obj0
    rw [hstep₁]
    simp only [Option.bind_eq_bind]
    dsimp only [Option.bind]
    rw [hstep₂]
    exact ⟨_, rfl, rfl⟩
  -- the formula names its one atom once
  have hφ : ∀ l x y, (OnlineReachSetAnalyzer.Formula.ap l x).IsSub
      (OnlineReachSetAnalyzer.Formula.until aux_I2 .tt (.ap "p" a) :
        OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) →
      (OnlineReachSetAnalyzer.Formula.ap l y).IsSub
      (OnlineReachSetAnalyzer.Formula.until aux_I2 .tt (.ap "p" a) :
        OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) → x = y := by
    intro l x y hx hy
    simp [OnlineReachSetAnalyzer.Formula.IsSub] at hx hy
    exact hx.2.trans hy.2.symm
  -- the claim would make the root `False` at `0` the satisfaction signal there
  obtain ⟨s, hs, root, hr, hv⟩ := H _ hφ true [(s₁, aux_I2, 0), (s₂, aux_J, 0)] (by simp)
    (by simp [hne₁, hne₂]) (aux_obj0 a) (by rw [Option.mem_def, aux_mk]) obj₂
    (by rw [Option.mem_def]; exact hrun)
  rw [hroot] at hr
  cases hr
  exact aux_sat a s₁ s₂ h₁' h₂' s hs ((hv 0 le_rfl).symm.trans hR₂0)

end main


section concrete

open scoped CORALean.Float
open Float

/-- Real `iterate` of halving from `1`. -/
private theorem aux_half_iter (n : ℕ) : -- --- CONCL ---
    ((FloatOps.half : ℝ → ℝ)^[n] FloatOps.one) = 1 / 2 ^ n := by -- --- PROOF ---
  induction n with
  | zero => simp [FloatOps.one]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    show 1 / 2 ^ n / 2 = _
    rw [div_div, pow_succ]

/-- The strict margin of comparisons over `ℝ` is `2⁻⁶⁴`. -/
private theorem aux_margin : (strictMargin : ℝ) = 1 / 2 ^ 64 := aux_half_iter 64

/-- Rounding up is exact over `ℝ`. -/
private theorem aux_mulUp (a b : ℝ) : FloatOps.mulUp a b = a * b := rfl

/-- Rounding down is exact over `ℝ`. -/
private theorem aux_mulDown (a b : ℝ) : FloatOps.mulDown a b = a * b := rfl

/-- The comparison over `ℝ` is the order. -/
private theorem aux_le (a b : ℝ) : FloatOps.le a b = decide (a ≤ b) := rfl

/-- The coordinates of a one-dimensional space. -/
private theorem aux_finRange : List.finRange 1 = [0] := rfl

/-- Two boxes are disjoint when some coordinate of one lies strictly beyond the other's. -/
private theorem aux_isDisjoint (I B : OnlineReachSetAnalyzer.boxes 1) :
    IsDisjoint.isDisjoint I B = (List.finRange 1).any fun j =>
      ltStrict (B.sup j) (I.inf j) || ltStrict (I.sup j) (B.inf j) := rfl

/-- A box contains another when every coordinate of the other lies inside. -/
private theorem aux_contains (I B : OnlineReachSetAnalyzer.boxes 1) :
    Contains.contains I B = (List.finRange 1).all fun j =>
      FloatOps.le (I.inf j) (B.inf j) && FloatOps.le (B.sup j) (I.sup j) := rfl

/-- The atom `x₀ ∈ [-10, 0]` in all locations. Noncomputable: its bounds are real numbers. -/
private noncomputable def aux_atom : AtomicProposition OnlineReachSetAnalyzer.boxes 1 :=
  ⟨1, ⟨fun _ => -10, fun _ => 0⟩, id, []⟩

/-- The box `[1, 2]`, outside the atom. -/
private def aux_s₁ : OnlineReachSetAnalyzer.boxes 1 := ⟨fun _ => 1, fun _ => 2⟩

/-- The box `[-1, 1]`, straddling the atom. -/
private def aux_s₂ : OnlineReachSetAnalyzer.boxes 1 := ⟨fun _ => -1, fun _ => 1⟩

/-- The atom is false on the box `[1, 2]`. -/
private theorem aux_h₁ : -- --- CONCL ---
    Kleene.ff ∈ OnlineAnalyzerNode.apValue (𝕋 := ℝ) aux_atom aux_s₁ 0 := by -- --- PROOF ---
  show OnlineAnalyzerNode.apValue (𝕋 := ℝ) aux_atom aux_s₁ 0 = some Kleene.ff
  -- the box projects to itself, and its distance to the atom decides both bounds
  simp [OnlineAnalyzerNode.apValue, AtomicProposition.canBeTrue, AtomicProposition.canBeFalse,
    aux_atom, aux_s₁, ContSet.project, AtomicProposition.containsLoc, Mtimes.mtimes,
    Float.Interval.mtimes, aux_mulUp, aux_mulDown, Float.sumUp, Float.sumDown]
  erw [aux_isDisjoint, aux_contains]
  simp [Float.ltStrict, aux_le, aux_margin, aux_finRange]
  repeat erw [Matrix.of_apply]
  norm_num

/-- The atom is unknown on the box `[-1, 1]`. -/
private theorem aux_h₂ : -- --- CONCL ---
    Kleene.uu ∈ OnlineAnalyzerNode.apValue (𝕋 := ℝ) aux_atom aux_s₂ 0 := by -- --- PROOF ---
  show OnlineAnalyzerNode.apValue (𝕋 := ℝ) aux_atom aux_s₂ 0 = some Kleene.uu
  -- the box meets the atom without lying inside it
  simp [OnlineAnalyzerNode.apValue, AtomicProposition.canBeTrue, AtomicProposition.canBeFalse,
    aux_atom, aux_s₂, ContSet.project, AtomicProposition.containsLoc, Mtimes.mtimes,
    Float.Interval.mtimes, aux_mulUp, aux_mulDown, Float.sumUp, Float.sumDown]
  erw [aux_isDisjoint, aux_contains]
  simp [Float.ltStrict, aux_le, aux_margin, aux_finRange]
  repeat erw [Matrix.of_apply]
  norm_num


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeSet_correct_counterexample : -- --- CONCL ---
    ¬ ∀ φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition OnlineReachSetAnalyzer.boxes 1),
      (∀ l x y, (OnlineReachSetAnalyzer.Formula.ap l x).IsSub φ →
        (OnlineReachSetAnalyzer.Formula.ap l y).IsSub φ → x = y) →
      ∀ (dp : Bool) (obs : List (OnlineReachSetAnalyzer.boxes 1 × STLInterval ℝ × ℕ)),
        obs ≠ [] → (∀ o ∈ obs, o.2.1 ≠ .empty) →
      ∀ obj₀ ∈ OnlineReachSetAnalyzer.mk? φ 1 dp,
        ∀ obj ∈ obs.foldlM (fun o x => o.observeSet (𝕋 := ℝ) 0 x.1 x.2.1 x.2.2) obj₀,
        ∃ s, φ.sat (OnlineReachSetAnalyzer.observeAtoms (𝕋 := ℝ)
            (fun _ => FourValuedSignal.uniformSignal .ii) obs) = some s ∧
          ∃ root, obj.nodes[0]? = some root ∧ ∀ t : ℝ, 0 ≤ t → root.signal.at t = s.at t
    := by -- --- PROOF ---
  exact aux_counterexample (𝕋 := ℝ) aux_atom aux_s₁ aux_s₂ aux_h₁ aux_h₂

end concrete

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
