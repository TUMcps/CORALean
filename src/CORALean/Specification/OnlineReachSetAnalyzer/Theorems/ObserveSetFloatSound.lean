module

public import CORALean.Specification.Kleene.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Theorems.UntilSpec
public import CORALean.Specification.KleeneSignal.Theorems.UntilMono
public import CORALean.Specification.KleeneSignal.Theorems.UntilFloatSound
public import CORALean.Specification.FourValuedSignal.Theorems.UntilSpec
public import CORALean.Specification.FourValuedSignal.Theorems.UntilRefines
public import CORALean.Specification.FourValuedSignal.Theorems.MinMaxSpec
public import CORALean.Specification.FourValuedSignal.Theorems.AtAnd
public import CORALean.Specification.FourValuedSignal.Theorems.AtOr
public import CORALean.Specification.FourValuedSignal.Theorems.AtAndTwo
public import CORALean.Specification.FourValuedSignal.Theorems.AtOrTwo
public import CORALean.Specification.FourValuedSignal.Theorems.AtNot
public import CORALean.Specification.FourValuedSignal.Theorems.AndMapTime
public import CORALean.Specification.FourValuedSignal.Theorems.OrMapTime
public import CORALean.Specification.FourValuedSignal.Theorems.MergeSpec
public import CORALean.Specification.FourValuedSignal.Theorems.SetSpec
public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalAt
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalSpec
public import CORALean.Specification.FourValuedSignal.Theorems.Basic
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.CombineFloatSound
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.ObserveSetFloatToRealNode
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.PropagateFloatToRealNode
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.SetPropagatedSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ObserveSetFloat
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ToRealAnalyzer
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.GetVerdictToRealAnalyzer
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.MkNodesSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveLeavesSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveSetCorrect
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveAtomsSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.SatRefines
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.UpdateNodeSpec
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet

@[expose] public section

/-!
# The float analyzer's conclusive verdicts are the exact ones

A run of `observeSetFloat`, with the inward-rounded until of the float propagation, from a float
analyzer that is the analyzer of `φ` read as reals, on observations with nonempty, pairwise
disjoint time intervals: wherever its verdict is `True` or `False`, the exact run on the
observations read as reals has that verdict [1, Alg. 1, Alg. 2]. The float state is not the exact
one, as it knows less where the until rounds; every `True` and `False` it holds is still the
four-valued semantics of its node's subformula on the observed atoms, which the exact root equals
(`observeSet_correct`). An `Unknown` verdict is not claimed.

## Inputs
* `eps` – tolerance of the float run
* `φ` – formula
* `dp` – whether to propagate down
* `obs` – observations: reachable set, float time interval, location

## Hypotheses
* `heps` – `eps` is `0` read as a real
* `hlabel` – a label names one atom in `φ`
* `hne` – at least one observation
* `hI` – every observation interval is nonempty
* `hdisj` – the observation intervals read as reals are pairwise disjoint

## Conclusion
* for a float analyzer that is the analyzer of `φ` read as reals, a float run on `obs` from it,
  and the exact run on `obs` read as reals: a `True` or `False` float verdict is the exact one

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


open Float SoundFloatArithmetic


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section untilRef

/-- The four-valued until at `t` is the join of the untils of the two refinements. -/
private theorem aux_until_at_eq_join (l r s : FourValuedSignal ℝ) (hl : l.IsValid)
    (hr : r.IsValid) (U : STLInterval ℝ) (hs : l.until U r = some s) (t : ℝ)
        (ht : 0 ≤ t) : -- --- CONCL ---
    s.at t = FourValued.join
        (((l.toKleeneSignal Kleene.ff).until U (r.toKleeneSignal Kleene.ff)).at t)
      (((l.toKleeneSignal Kleene.tt).until U (r.toKleeneSignal Kleene.tt)).at t)
    := by -- --- PROOF ---
  obtain ⟨s', hs', -, h⟩ := FourValuedSignal.until_spec l r hl hr U
  rw [hs] at hs'; cases hs'
  obtain ⟨h1, h2, -, -⟩ := h t ht
  unfold FourValued.join
  split_ifs with he
  · exact h2 he
  · exact h1.2 he

private theorem aux_floor_le_ceil (v : FourValued) : v.floor ≤ v.ceil := by
  cases v <;> simp [FourValued.floor, FourValued.ceil, Kleene.le_iff_code, Kleene.code]

/-- The until keeps `True` and `False`: where the operands' `True` and `False` are kept, so are
the until's. -/
private theorem aux_until_wref (l r l' r' s s' : FourValuedSignal ℝ) (hl : l.IsValid)
    (hr : r.IsValid) (hl' : l'.IsValid) (hr' : r'.IsValid) (U : STLInterval ℝ)
    (hs : l.until U r = some s) (hs' : l'.until U r' = some s')
    (h1 : ∀ x : ℝ, 0 ≤ x → (l.at x = .tt → l'.at x = .tt) ∧ (l.at x = .ff → l'.at x = .ff))
    (h2 : ∀ x : ℝ, 0 ≤ x → (r.at x = .tt → r'.at x = .tt) ∧
        (r.at x = .ff → r'.at x = .ff)) : -- --- CONCL ---
    ∀ t : ℝ, 0 ≤ t → (s.at t = .tt → s'.at t = .tt) ∧ (s.at t = .ff → s'.at t = .ff)
    := by -- --- PROOF ---
  intro t ht
  have vlf := (l.toKleeneSignal_spec hl Kleene.ff).1
  have vlt := (l.toKleeneSignal_spec hl Kleene.tt).1
  have vrf := (r.toKleeneSignal_spec hr Kleene.ff).1
  have vrt := (r.toKleeneSignal_spec hr Kleene.tt).1
  have vlf' := (l'.toKleeneSignal_spec hl' Kleene.ff).1
  have vlt' := (l'.toKleeneSignal_spec hl' Kleene.tt).1
  have vrf' := (r'.toKleeneSignal_spec hr' Kleene.ff).1
  have vrt' := (r'.toKleeneSignal_spec hr' Kleene.tt).1
  -- the refinements are valid, and the window lies after `t`
  have hge : ∀ t', t' - t ∈ U.set → t ≤ t' := fun t' h' => by
    have := STLInterval.zero_le_of_mem_set U _ h'; linarith
  -- floor and ceiling untils of the refined operands are ordered
  have m' := KleeneSignal.until_mono _ _ _ _ vlf' vlt' vrf' vrt' U
      (fun x hx => by
        rw [(l'.toKleeneSignal_at hl' x hx).1, (l'.toKleeneSignal_at hl' x hx).2]
        exact aux_floor_le_ceil _)
      (fun x hx => by
        rw [(r'.toKleeneSignal_at hr' x hx).1, (r'.toKleeneSignal_at hr' x hx).2]
        exact aux_floor_le_ceil _) t ht
  have m := KleeneSignal.until_mono _ _ _ _ vlf vlt vrf vrt U
      (fun x hx => by
        rw [(l.toKleeneSignal_at hl x hx).1, (l.toKleeneSignal_at hl x hx).2]
        exact aux_floor_le_ceil _)
      (fun x hx => by
        rw [(r.toKleeneSignal_at hr x hx).1, (r.toKleeneSignal_at hr x hx).2]
        exact aux_floor_le_ceil _) t ht
  -- the until is the join of its floor and ceiling untils
  rw [aux_until_at_eq_join l r s hl hr U hs t ht, aux_until_at_eq_join l' r' s' hl' hr' U hs' t ht]
  set Fl := (l.toKleeneSignal Kleene.ff).until U (r.toKleeneSignal Kleene.ff) with hFl
  set Cl := (l.toKleeneSignal Kleene.tt).until U (r.toKleeneSignal Kleene.tt) with hCl
  set Fl' := (l'.toKleeneSignal Kleene.ff).until U (r'.toKleeneSignal Kleene.ff) with hFl'
  set Cl' := (l'.toKleeneSignal Kleene.tt).until U (r'.toKleeneSignal Kleene.tt) with hCl'
  -- the characterizations of `True` and `False` of the Kleene untils
  obtain ⟨-, kf⟩ := KleeneSignal.until_spec _ _ vlf vrf U
  obtain ⟨-, kt⟩ := KleeneSignal.until_spec _ _ vlt vrt U
  obtain ⟨-, kf'⟩ := KleeneSignal.until_spec _ _ vlf' vrf' U
  obtain ⟨-, kt'⟩ := KleeneSignal.until_spec _ _ vlt' vrt' U
  obtain ⟨kf1, -⟩ := kf t ht
  obtain ⟨-, kt2⟩ := kt t ht
  obtain ⟨kf1', -⟩ := kf' t ht
  obtain ⟨-, kt2'⟩ := kt' t ht
  -- the floor is `True` exactly where the signal is, the ceiling `False` likewise
  have flo : ∀ (a : FourValuedSignal ℝ) (ha : a.IsValid) x, 0 ≤ x →
      ((a.toKleeneSignal Kleene.ff).at x = .tt ↔ a.at x = .tt) := by
    intro a ha x hx; rw [(a.toKleeneSignal_at ha x hx).1]
    cases a.at x <;> simp [FourValued.floor]
  have cei : ∀ (a : FourValuedSignal ℝ) (ha : a.IsValid) x, 0 ≤ x →
      ((a.toKleeneSignal Kleene.tt).at x = .ff ↔ a.at x = .ff) := by
    intro a ha x hx; rw [(a.toKleeneSignal_at ha x hx).2]
    cases a.at x <;> simp [FourValued.ceil]
  have fkt : ∀ k : Kleene, FourValued.fromKleene k = .tt → k = .tt := by
    intro k; cases k <;> simp [FourValued.fromKleene]
  have fkf : ∀ k : Kleene, FourValued.fromKleene k = .ff → k = .ff := by
    intro k; cases k <;> simp [FourValued.fromKleene]
  constructor
  · intro h
    unfold FourValued.join at h ⊢
    split_ifs at h with he
    · -- the floor until is `True`: a witness with `True` operands, kept by the refinement
      have hF : Fl.at t = .tt := fkt _ h
      obtain ⟨t', h1', h2', h3'⟩ := kf1.1 hF
      have hF' : Fl'.at t = .tt := by
        refine kf1'.2 ⟨t', h1', ?_, fun x hx1 hx2 => ?_⟩
        · have h0 : 0 ≤ t' := ht.trans (hge t' h1')
          exact (flo r' hr' t' h0).2 ((h2 t' h0).1 ((flo r hr t' h0).1 h2'))
        · have h0 : 0 ≤ x := ht.trans hx1.le
          exact (flo l' hl' x h0).2 ((h1 x h0).1 ((flo l hl x h0).1 (h3' x hx1 hx2)))
      have hC' : Cl'.at t = .tt := by
        have := m'; rw [hF'] at this
        revert this; generalize Cl'.at t = x
        cases x <;> simp [Kleene.le_iff_code, Kleene.code]
      rw [hF', hC', if_pos rfl]; rfl
  · intro h
    unfold FourValued.join at h ⊢
    split_ifs at h with he
    · -- the ceiling until is `False`: every witness fails, kept by the refinement
      have hC : Cl.at t = .ff := by
        rw [← he]; exact fkf _ h
      have hC' : Cl'.at t = .ff := by
        refine kt2'.2 fun t' h1' => ?_
        have h0 : 0 ≤ t' := ht.trans (hge t' h1')
        rcases kt2.1 hC t' h1' with h' | ⟨x, hx1, hx2, hx3⟩
        · exact Or.inl ((cei r' hr' t' h0).2 ((h2 t' h0).2 ((cei r hr t' h0).1 h')))
        · have hx0 : 0 ≤ x := ht.trans hx1.le
          exact Or.inr ⟨x, hx1, hx2, (cei l' hl' x hx0).2 ((h1 x hx0).2 ((cei l hl x hx0).1 hx3))⟩
      have hF' : Fl'.at t = .ff := by
        have := m'; rw [hC'] at this
        revert this; generalize Fl'.at t = x
        cases x <;> simp [Kleene.le_iff_code, Kleene.code]
      rw [hF', hC', if_pos rfl]; rfl

end untilRef


section weak
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {A : Type}

/-- `sem` keeps every `True` and `False` of `s`. -/
private def aux_WRef (sem s : FourValuedSignal ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (s.at t = .tt → sem.at t = .tt) ∧ (s.at t = .ff → sem.at t = .ff)

/-- A refinement of `sem` keeps what `sem` keeps. -/
private theorem aux_wref_trans {sem sem' s : FourValuedSignal ℝ} (h : sem'.Refines sem)
    (hw : aux_WRef sem s) : aux_WRef sem' s := fun t ht =>
  ⟨fun e => by have e' := (hw t ht).1 e; rw [h t ht (by rw [e']; nofun), e'],
   fun e => by have e' := (hw t ht).2 e; rw [h t ht (by rw [e']; nofun), e']⟩

/-- A merge of two signals whose `True` and `False` `sem` keeps. -/
private theorem aux_wref_merge {sem a Δ : FourValuedSignal ℝ} (ha : a.IsValid) (hd : Δ.IsValid)
    (h1 : aux_WRef sem a) (h2 : aux_WRef sem Δ) : -- --- CONCL ---
    aux_WRef sem (a.merge Δ)
    := by -- --- PROOF ---
  intro t ht
  obtain ⟨-, hm⟩ := FourValuedSignal.merge_spec a Δ ha hd
  by_cases hi : Δ.at t = .ii
  · rw [(hm t ht).2 hi]; exact h1 t ht
  · rw [(hm t ht).1 hi]; exact h2 t ht

/-- The float `Combine` of children valid as reals is valid as reals. -/
private theorem aux_combineFloat_valid (n : OnlineAnalyzerNode 𝕋 A)
    (ch : List (OnlineAnalyzerNode 𝕋 A))
    (hch : ∀ c ∈ ch, (c.signal.mapTime toReal).IsValid) : -- --- CONCL ---
    ∀ df ∈ n.combineFloat ch, (df.mapTime toReal).IsValid := by -- --- PROOF ---
  intro df hdf
  -- by the operator of the node; a leaf combines nothing
  unfold OnlineAnalyzerNode.combineFloat at hdf
  cases hkind : n.kind <;> rw [hkind] at hdf <;> dsimp only at hdf
  · exact absurd hdf (by simp)
  · exact absurd hdf (by simp)
  · exact absurd hdf (by simp)
  · -- `¬`: the negation reads the time stamps exactly
    rcases ch with _ | ⟨c, _ | ⟨c', rest⟩⟩
    · exact absurd hdf (by simp)
    · obtain rfl := Option.some.inj hdf
      rw [FourValuedSignal.not_mapTime]
      exact FourValuedSignal.not_isValid _ (hch c (by simp))
    · exact absurd hdf (by simp)
  · by_cases he : ch = []
    · subst he; exact absurd hdf (by simp)
    rw [if_neg (by simpa using he)] at hdf
    haveI : Nonempty (Fin ch.length) := ⟨⟨0, List.length_pos_iff.2 he⟩⟩
    -- `∨`: the float disjunction read as reals is the exact one, valid
    obtain ⟨r, hr, hrv, -⟩ := FourValuedSignal.at_or
      (fun k : Fin ch.length => (ch.get k).signal.mapTime toReal)
      (fun k => hch _ (List.get_mem ch k))
    rw [← FourValuedSignal.or_mapTime, hdf, Option.map_some, Option.some.injEq] at hr
    rw [hr]; exact hrv
  · by_cases he : ch = []
    · subst he; exact absurd hdf (by simp)
    rw [if_neg (by simpa using he)] at hdf
    haveI : Nonempty (Fin ch.length) := ⟨⟨0, List.length_pos_iff.2 he⟩⟩
    -- `∧`: likewise
    obtain ⟨r, hr, hrv, -⟩ := FourValuedSignal.at_and
      (fun k : Fin ch.length => (ch.get k).signal.mapTime toReal)
      (fun k => hch _ (List.get_mem ch k))
    rw [← FourValuedSignal.and_mapTime, hdf, Option.map_some, Option.some.injEq] at hr
    rw [hr]; exact hrv
  · rcases ch with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, rest⟩⟩⟩
    · simp at hdf
    · simp at hdf
    swap
    · simp at hdf
    rcases hI : n.interval with _ | U
    · rw [hI] at hdf; exact absurd hdf (by simp)
    rw [hI] at hdf
    -- `U_I`: the two float Kleene untils read as reals are valid, and so is their pair
    have hl := hch c1 (by simp)
    have hr := hch c2 (by simp)
    have hlf := (FourValuedSignal.toKleeneSignal_spec _ hl Kleene.ff).1
    have hrf' := (FourValuedSignal.toKleeneSignal_spec _ hr Kleene.ff).1
    have hlt := (FourValuedSignal.toKleeneSignal_spec _ hl Kleene.tt).1
    have hrt := (FourValuedSignal.toKleeneSignal_spec _ hr Kleene.tt).1
    rw [← FourValuedSignal.toKleeneSignal_mapTime] at hlf hlt
    rw [← FourValuedSignal.toKleeneSignal_mapTime] at hrf' hrt
    obtain ⟨hvmn, -⟩ := KleeneSignal.untilFloat_sound _ _ hlf hrf' U
    obtain ⟨hvmx, -⟩ := KleeneSignal.untilFloat_sound _ _ hlt hrt U
    -- the float result is the minimal until with the set where the two untils differ
    simp only [FourValuedSignal.untilFloat, Option.mem_def, Option.map_eq_some_iff] at hdf
    obtain ⟨inc, hinc, rfl⟩ := hdf
    set mn := (c1.signal.toKleeneSignal Kleene.ff).untilFloat U (c2.signal.toKleeneSignal Kleene.ff)
    set mx := (c1.signal.toKleeneSignal Kleene.tt).untilFloat U (c2.signal.toKleeneSignal Kleene.tt)
    have hK : (KleeneSignal.combine (fun (args : Fin 2 → Kleene) (_ : Unit) =>
        Kleene.fromBool (decide (args 0 ≠ args 1))) ![mn, mx] ()).mapTime toReal =
        KleeneSignal.combine (fun (args : Fin 2 → Kleene) (_ : Unit) =>
          Kleene.fromBool (decide (args 0 ≠ args 1)))
          ![mn.mapTime toReal, mx.mapTime toReal] () := by
      rw [KleeneSignal.combine_mapTime]; congr 1; funext k; fin_cases k <;> rfl
    obtain ⟨inc', hinc', hv, -⟩ := FourValuedSignal.minMax_spec _ _ _ hvmn hvmx hK
    rw [KleeneSignal.toBoolSignal?_mapTime, hinc, Option.map_some, Option.some.injEq] at hinc'
    subst hinc'
    exact hv

end weak


section comb
variable {A : Type}

/-- `¬` keeps `True` and `False`. -/
private theorem aux_fv_not (a a' : FourValued) (h : (a = .tt → a' = .tt) ∧ (a = .ff → a' = .ff)) :
    (a.not = .tt → a'.not = .tt) ∧ (a.not = .ff → a'.not = .ff) := by
  cases a <;> cases a' <;> simp_all [FourValued.not]

/-- `∧` keeps `True` and `False`. -/
private theorem aux_fv_and (a b a' b' : FourValued)
    (ha : (a = .tt → a' = .tt) ∧ (a = .ff → a' = .ff))
    (hb : (b = .tt → b' = .tt) ∧ (b = .ff → b' = .ff)) : -- --- CONCL ---
    (a.and b = .tt → a'.and b' = .tt) ∧ (a.and b = .ff → a'.and b' = .ff) := by -- --- PROOF ---
  have hi : ∀ x y : FourValued, (x.and y = .tt ↔ x = .tt ∧ y = .tt) ∧
      (x.and y = .ff ↔ x = .ff ∨ y = .ff) := by
    intro x y; cases x <;> cases y <;> simp [FourValued.and]
  rw [(hi a b).1, (hi a b).2, (hi a' b').1, (hi a' b').2]
  exact ⟨fun h => ⟨ha.1 h.1, hb.1 h.2⟩, fun h => h.elim (fun h => Or.inl (ha.2 h))
    (fun h => Or.inr (hb.2 h))⟩

/-- `∨` keeps `True` and `False`. -/
private theorem aux_fv_or (a b a' b' : FourValued)
    (ha : (a = .tt → a' = .tt) ∧ (a = .ff → a' = .ff))
    (hb : (b = .tt → b' = .tt) ∧ (b = .ff → b' = .ff)) : -- --- CONCL ---
    (a.or b = .tt → a'.or b' = .tt) ∧ (a.or b = .ff → a'.or b' = .ff) := by -- --- PROOF ---
  have hi : ∀ x y : FourValued, (x.or y = .tt ↔ x = .tt ∨ y = .tt) ∧
      (x.or y = .ff ↔ x = .ff ∧ y = .ff) := by
    intro x y; cases x <;> cases y <;> simp [FourValued.or]
  rw [(hi a b).1, (hi a b).2, (hi a' b').1, (hi a' b').2]
  exact ⟨fun h => h.elim (fun h => Or.inl (ha.1 h)) (fun h => Or.inr (hb.1 h)),
    fun h => ⟨ha.2 h.1, hb.2 h.2⟩⟩

/-- `Combine` at an inner node of `ψ k` succeeds, and the semantics keeps its `True` and `False`
where it keeps the children's. -/
private theorem aux_combine_wref (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (sig : A → FourValuedSignal ℝ) (sem : ℕ → FourValuedSignal ℝ) (k : ℕ)
    (n : OnlineAnalyzerNode ℝ A) (get : ℕ → OnlineAnalyzerNode ℝ A)
    (hshape : OnlineReachSetAnalyzer.IsNodeOf ψ (ψ k) n) (hk : (ψ k).sat sig = some (sem k))
    (hsem : ∀ c ∈ n.children, (ψ c).sat sig = some (sem c) ∧ (sem c).IsValid)
    (hval : ∀ c ∈ n.children, (get c).signal.IsValid) (hinner : n.children ≠ []) : -- --- CONCL ---
    ∃ Δ, n.combine (n.children.map get) = some Δ ∧ Δ.IsValid ∧
      ((∀ c ∈ n.children, aux_WRef (sem c) (get c).signal) → aux_WRef (sem k) Δ)
    := by -- --- PROOF ---
  -- by the operator of the node; a leaf has no children
  unfold OnlineReachSetAnalyzer.IsNodeOf at hshape
  split at hshape
  · exact absurd hshape.2 hinner
  · exact absurd hshape.2 hinner
  · exact absurd hshape.2.1 hinner
  · -- `¬`: the child and its semantics
    rename_i φ hφ
    obtain ⟨hkind, c, hc, hψ⟩ := hshape
    rw [hc] at hsem hval ⊢
    obtain ⟨hsc, hscv⟩ := hsem c (by simp)
    have hv := hval c (by simp)
    rw [hφ] at hk
    simp only [OnlineReachSetAnalyzer.Formula.sat, ← hψ, hsc, Option.map_some,
      Option.some.injEq] at hk
    rw [← hk]
    -- the negation of the child's signal; `¬` keeps `True` and `False`
    refine ⟨(get c).signal.not, by simp [OnlineAnalyzerNode.combine, hkind],
      FourValuedSignal.not_isValid _ hv, fun hw t ht => ?_⟩
    rw [FourValuedSignal.at_not _ hv, FourValuedSignal.at_not _ hscv]
    exact aux_fv_not _ _ (hw c (by simp) t ht)
  · rename_i φ φ' hφ
    obtain ⟨hkind, c, c', hc, hψ, hψ'⟩ := hshape
    rw [hc] at hsem hval ⊢
    obtain ⟨hsc, hscv⟩ := hsem c (by simp)
    obtain ⟨hsc', hscv'⟩ := hsem c' (by simp)
    have hv := hval c (by simp)
    have hv' := hval c' (by simp)
    rw [hφ] at hk
    simp only [OnlineReachSetAnalyzer.Formula.sat, ← hψ, ← hψ', hsc, hsc', Option.bind_some] at hk
    -- the conjunction of the children's signals, and of their semantics
    obtain ⟨a, ha, hav, ha'⟩ := FourValuedSignal.at_and_two ![(get c).signal, (get c').signal]
      (by intro k; fin_cases k <;> simpa)
    obtain ⟨b, hb, -, hb'⟩ := FourValuedSignal.at_and_two ![sem c, sem c']
      (by intro k; fin_cases k <;> simpa)
    rw [hb] at hk; cases hk
    refine ⟨a, ?_, hav, fun hw t ht => ?_⟩
    · simp only [OnlineAnalyzerNode.combine, hkind, List.map_cons, List.map_nil]
      rw [if_neg (by simp)]
      rw [← ha]; congr 1; funext i; fin_cases i <;> rfl
    · rw [ha' t ht, hb' t ht]
      exact aux_fv_and _ _ _ _ (hw c (by simp) t ht) (hw c' (by simp) t ht)
  · rename_i φ φ' hφ
    obtain ⟨hkind, c, c', hc, hψ, hψ'⟩ := hshape
    rw [hc] at hsem hval ⊢
    obtain ⟨hsc, hscv⟩ := hsem c (by simp)
    obtain ⟨hsc', hscv'⟩ := hsem c' (by simp)
    have hv := hval c (by simp)
    have hv' := hval c' (by simp)
    rw [hφ] at hk
    simp only [OnlineReachSetAnalyzer.Formula.sat, ← hψ, ← hψ', hsc, hsc', Option.bind_some] at hk
    -- the disjunction of the children's signals, and of their semantics
    obtain ⟨a, ha, hav, ha'⟩ := FourValuedSignal.at_or_two ![(get c).signal, (get c').signal]
      (by intro k; fin_cases k <;> simpa)
    obtain ⟨b, hb, -, hb'⟩ := FourValuedSignal.at_or_two ![sem c, sem c']
      (by intro k; fin_cases k <;> simpa)
    rw [hb] at hk; cases hk
    refine ⟨a, ?_, hav, fun hw t ht => ?_⟩
    · simp only [OnlineAnalyzerNode.combine, hkind, List.map_cons, List.map_nil]
      rw [if_neg (by simp)]
      rw [← ha]; congr 1; funext i; fin_cases i <;> rfl
    · rw [ha' t ht, hb' t ht]
      exact aux_fv_or _ _ _ _ (hw c (by simp) t ht) (hw c' (by simp) t ht)
  · rename_i I φ φ' hφ
    obtain ⟨hkind, hI, c, c', hc, hψ, hψ'⟩ := hshape
    rw [hc] at hsem hval ⊢
    obtain ⟨hsc, hscv⟩ := hsem c (by simp)
    obtain ⟨hsc', hscv'⟩ := hsem c' (by simp)
    have hv := hval c (by simp)
    have hv' := hval c' (by simp)
    rw [hφ] at hk
    simp only [OnlineReachSetAnalyzer.Formula.sat, ← hψ, ← hψ', hsc, hsc', Option.bind_some] at hk
    -- the untils exist, and the semantics keeps the until's `True` and `False`
    obtain ⟨a, b, ha, hb, hav, -, -, -⟩ := FourValuedSignal.until_refines (get c).signal
      (get c').signal (sem c) (sem c') hv hv' hscv hscv' I
    rw [hb] at hk; cases hk
    refine ⟨a, by simp [OnlineAnalyzerNode.combine, hkind, hI, ha], hav, fun hw t ht => ?_⟩
    exact aux_until_wref _ _ _ _ _ _ hv hv' hscv hscv' I ha hb (fun x hx => hw c (by simp) x hx)
      (fun x hx => hw c' (by simp) x hx) t ht

end comb


section prop
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {A : Type}

/-- A successful `mapM` relates each input to its output. -/
private theorem aux_mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by simp at h; subst h; exact List.Forall₂.nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp [hfa, hl] at h; subst h
        exact List.Forall₂.cons hfa (aux_mapM_forall₂ f l bs hl)

/-- Two `Forall₂` compose. -/
private theorem aux_forall₂_comp {α β γ : Type} {R1 : α → β → Prop} {R2 : β → γ → Prop} :
    ∀ {l1 : List α} {l2 : List β} {l3 : List γ}, List.Forall₂ R1 l1 l2 → List.Forall₂ R2 l2 l3 →
      List.Forall₂ (fun a c => ∃ b, R1 a b ∧ R2 b c) l1 l3
  | [], [], [], _, _ => List.Forall₂.nil
  | _ :: _, _ :: _, _ :: _, List.Forall₂.cons h1 t1, List.Forall₂.cons h2 t2 =>
    List.Forall₂.cons ⟨_, h1, h2⟩ (aux_forall₂_comp t1 t2)

/-- Writing `bs` at the positions `cl` puts at `j` an element related to `j + 1` if `j + 1 ∈ cl`,
and leaves it otherwise. -/
private theorem aux_foldl_set {B : Type} (R : ℕ → B → Prop) :
    ∀ (cl : List ℕ) (bs : List B), List.Forall₂ R cl bs → ∀ (base : List B),
      (∀ c ∈ cl, 1 ≤ c ∧ c - 1 < base.length) →
      ((cl.zip bs).foldl (fun ns p => ns.set (p.1 - 1) p.2) base).length = base.length ∧
      ∀ j, j < base.length →
        (j + 1 ∈ cl → ∃ b, ((cl.zip bs).foldl (fun ns p => ns.set (p.1 - 1) p.2) base)[j]? =
          some b ∧ R (j + 1) b) ∧
        (j + 1 ∉ cl → ((cl.zip bs).foldl (fun ns p => ns.set (p.1 - 1) p.2) base)[j]? = base[j]?)
  | [], [], _, base, _ => by simp
  | c :: cl, b :: bs, h, base, hcl => by
    cases h with
    | cons hR h =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      have hc := hcl c (by simp)
      obtain ⟨ih1, ih2⟩ := aux_foldl_set R cl bs h (base.set (c - 1) b)
        (fun c' hc' => by simpa using hcl c' (by simp [hc']))
      simp only [List.length_set] at ih1 ih2
      -- the head is written first, the rest of the fold overwrites it only at its own positions
      refine ⟨ih1, fun j hj => ⟨fun hmem => ?_, fun hmem => ?_⟩⟩
      · by_cases hin : j + 1 ∈ cl
        · exact (ih2 j hj).1 hin
        · rw [(ih2 j hj).2 hin]
          have : c = j + 1 := by -- `c` is the one index of the head
            rcases List.mem_cons.1 hmem with h | h
            · exact h.symm
            · exact absurd h hin
          subst this
          exact ⟨b, by simp [hj], hR⟩
      · rw [(ih2 j hj).2 (fun h' => hmem (by simp [h']))]
        rw [List.getElem?_set_ne]
        intro h'; apply hmem; simp; left; omega

/-- Mapping commutes with writing at positions. -/
private theorem aux_map_foldl_set {α β : Type} (g : α → β) :
    ∀ (cl : List ℕ) (bs : List α) (base : List α),
      ((cl.zip bs).foldl (fun ns p => ns.set (p.1 - 1) p.2) base).map g =
        (cl.zip (bs.map g)).foldl (fun ns p => ns.set (p.1 - 1) p.2) (base.map g)
  | [], _, base => by simp
  | _ :: _, [], base => by simp
  | c :: cl, b :: bs, base => by
    simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons]
    rw [aux_map_foldl_set g cl bs (base.set (c - 1) b), List.map_set]

/-- Being the node of `φ` reads only the kind, the children, the interval and the atom. -/
private theorem aux_shapeOf_congr (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (φ : OnlineReachSetAnalyzer.Formula ℝ A) (n n' : OnlineAnalyzerNode ℝ A)
    (h1 : n'.kind = n.kind) (h2 : n'.children = n.children) (h3 : n'.interval = n.interval)
    (h4 : n'.ap = n.ap) (h : OnlineReachSetAnalyzer.IsNodeOf ψ φ n) : -- --- CONCL ---
    OnlineReachSetAnalyzer.IsNodeOf ψ φ n' := by -- --- PROOF ---
  cases φ <;> simp only [OnlineReachSetAnalyzer.IsNodeOf] at h ⊢ <;> rw [h1, h2] <;>
    (try rw [h4]) <;> (try rw [h3]) <;> exact h

/-- The float nodes read as reals: the syntax DAG of `ψ`, valid, and every `True` and `False` the
semantics of the node's formula. -/
private structure aux_FInv (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (sem : ℕ → FourValuedSignal ℝ)
    (R : List (OnlineAnalyzerNode ℝ A)) : Prop where
  dag : ∀ j (h : j < R.length), R[j].idx = j + 1 ∧
    OnlineReachSetAnalyzer.IsNodeOf ψ (ψ (j + 1)) R[j] ∧
    ∀ c ∈ R[j].children, 1 ≤ c ∧ c - 1 < R.length
  valid : ∀ j (h : j < R.length), R[j].signal.IsValid
  wsound : ∀ j (h : j < R.length), aux_WRef (sem (j + 1)) R[j].signal

/-- `y` is `x` with another signal, valid and with `True` and `False` the semantics keeps. -/
private def aux_Upd (sem : ℕ → FourValuedSignal ℝ) (j : ℕ) (x y : OnlineAnalyzerNode ℝ A) : Prop :=
  y.idx = x.idx ∧ y.kind = x.kind ∧ y.children = x.children ∧ y.interval = x.interval ∧
    y.ap = x.ap ∧ y.signal.IsValid ∧ aux_WRef (sem (j + 1)) y.signal

/-- Updating every node so keeps the invariant. -/
private theorem aux_finv_of_upd (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (sem : ℕ → FourValuedSignal ℝ)
    (R R' : List (OnlineAnalyzerNode ℝ A)) (inv : aux_FInv ψ sem R) (hlen : R'.length = R.length)
    (hu : ∀ j (h : j < R.length) (h' : j < R'.length), aux_Upd sem j R[j] R'[j]) : -- --- CONCL ---
    aux_FInv ψ sem R' := by -- --- PROOF ---
  refine ⟨fun j h => ?_, fun j h => (hu j (hlen ▸ h) h).2.2.2.2.2.1,
    fun j h => (hu j (hlen ▸ h) h).2.2.2.2.2.2⟩
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := hu j (hlen ▸ h) h
  obtain ⟨d1, d2, d3⟩ := inv.dag j (hlen ▸ h)
  refine ⟨by rw [u1, d1], aux_shapeOf_congr ψ _ _ _ u2 u3 u4 u5 d2, fun c hc => ?_⟩
  rw [u3] at hc
  rw [hlen]; exact d3 c hc

/-- A node is an update of itself. -/
private theorem aux_upd_refl (sem : ℕ → FourValuedSignal ℝ) (j : ℕ) (x : OnlineAnalyzerNode ℝ A)
    (hv : x.signal.IsValid) (hw : aux_WRef (sem (j + 1)) x.signal) : aux_Upd sem j x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, hv, hw⟩

/-- `setPropagated` is an update: it erases at most. -/
private theorem aux_upd_setPropagated (sem : ℕ → FourValuedSignal ℝ) (j : ℕ)
    (x y : OnlineAnalyzerNode ℝ A)
    (p : ℕ) (P : STLInterval ℝ) (hv : x.signal.IsValid) (hw : aux_WRef (sem (j + 1)) x.signal)
    (h : x.setPropagated 0 p P = some y) : -- --- CONCL ---
    aux_Upd sem j x y
    := by -- --- PROOF ---
  obtain ⟨yv, -, hnd, hd⟩ := OnlineAnalyzerNode.setPropagated_spec 0 x hv p P y h
  have hfields : y.idx = x.idx ∧ y.kind = x.kind ∧ y.children = x.children ∧
      y.interval = x.interval ∧ y.ap = x.ap ∧ y.dropPropagated = x.dropPropagated := by
    unfold OnlineAnalyzerNode.setPropagated at h
    dsimp only at h
    split at h
    · cases h
    · split_ifs at h <;> cases h <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hfields
  refine ⟨f1, f2, f3, f4, f5, yv, fun t ht => ?_⟩
  cases hdp : x.dropPropagated
  · rw [hnd hdp]; exact hw t ht
  · by_cases hE : t ∈ (y.getAllProp 0).set
    · rw [((hd hdp) t ht).1 hE]; exact ⟨fun e => absurd e (by nofun), fun e => absurd e (by nofun)⟩
    · rw [((hd hdp) t ht).2 hE]; exact hw t ht

end prop


section prop2
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {A : Type}

/-- A `Forall₂` of `f a = some b` makes the right list the map of `f`, read with a default. -/
private theorem aux_forall₂_map {α β : Type} (f : α → Option β) (d : β) {l : List α} {l' : List β}
    (h : List.Forall₂ (fun a b => f a = some b) l l') : l' = l.map fun a => (f a).getD d := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

/-- One float step at node `k`: the node merges the float `Δ`, its children are erased on the
conclusive interval; the invariant holds after. -/
private theorem aux_fstep (eps : 𝕋) (heps : toReal eps = 0)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A) (sig : A → FourValuedSignal ℝ)
    (sem : ℕ → FourValuedSignal ℝ) (F : List (OnlineAnalyzerNode 𝕋 A))
    (hsem : ∀ i, 1 ≤ i → i ≤ F.length → (ψ i).sat sig = some (sem i) ∧ (sem i).IsValid)
    (inv : aux_FInv ψ sem (F.map OnlineAnalyzerNode.toRealNode)) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k - 1 < F.length) (cs : List (OnlineAnalyzerNode 𝕋 A))
    (hcs : F[k - 1].children.mapM (fun c => F[c - 1]?) = some cs)
    (r : OnlineAnalyzerNode 𝕋 A × List (OnlineAnalyzerNode 𝕋 A))
    (hr : F[k - 1].propagateFloat eps cs .empty = some r) : -- --- CONCL ---
    aux_FInv ψ sem (((F[k - 1].children.zip r.2).foldl (fun ns p => ns.set (p.1 - 1) p.2)
      (F.set (k - 1) r.1)).map OnlineAnalyzerNode.toRealNode) ∧
    ((F[k - 1].children.zip r.2).foldl (fun ns p => ns.set (p.1 - 1) p.2)
      (F.set (k - 1) r.1)).length = F.length := by -- --- PROOF ---
  set n := F[k - 1] with hn
  set R := F.map OnlineAnalyzerNode.toRealNode with hR
  -- the node, its DAG facts and its children's nodes
  have hkk : k - 1 + 1 = k := by omega
  have hRl : R.length = F.length := by simp [R]
  have hRj : ∀ j (h : j < F.length), R[j]'(by rw [hRl]; exact h) = F[j].toRealNode := by
    intro j h; simp [R]
  obtain ⟨d1, d2, d3⟩ := inv.dag (k - 1) (by rw [hRl]; exact hk)
  rw [hRj _ hk] at d1 d2 d3
  rw [hkk] at d2
  have hrange : ∀ c ∈ n.children, 1 ≤ c ∧ c - 1 < F.length := fun c hc => by
    have := d3 c hc; rw [hRl] at this; exact this
  have hF := aux_mapM_forall₂ _ _ _ hcs
  have hcs' : cs = n.children.map fun c => F[c - 1]?.getD n :=
    aux_forall₂_map (fun c => F[c - 1]?) n hF
  have hget : ∀ c (hc : c ∈ n.children), F[c - 1]?.getD n = F[c - 1]'(hrange c hc).2 := by
    intro c hc; simp [(hrange c hc).2]
  -- the float step read as reals
  obtain ⟨hleaf, hinner⟩ := OnlineAnalyzerNode.propagateFloat_toRealNode eps n cs .empty
  have hkn : n.toRealNode.kind = n.kind := rfl
  change OnlineReachSetAnalyzer.IsNodeOf ψ (ψ k) n.toRealNode at d2
  rw [← List.length_map (f := OnlineAnalyzerNode.toRealNode), aux_map_foldl_set, List.map_set]
  by_cases hkl : n.kind = .true ∨ n.kind = .false ∨ n.kind = .ap
  · -- a leaf: no children, and the node read as reals is kept
    have e := hleaf hkl
    rw [hr] at e
    have hprop : n.toRealNode.propagate (toReal eps) (cs.map OnlineAnalyzerNode.toRealNode)
        (STLInterval.empty : STLInterval 𝕋).toRealInterval =
        some (n.toRealNode, cs.map OnlineAnalyzerNode.toRealNode) := by
      unfold OnlineAnalyzerNode.propagate
      have hk' : n.toRealNode.kind = n.kind := rfl
      rw [hk']
      rcases hkl with h | h | h <;> rw [h]
      rcases n.toRealNode.tentative <;> rfl
    rw [hprop, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    -- a leaf has no children
    have hch : n.toRealNode.children = [] := by
      rcases hkl with h | h | h <;>
        cases hψ : ψ k <;> rw [hψ] at d2 <;> simp only [OnlineReachSetAnalyzer.IsNodeOf] at d2 <;>
        first | exact d2.2 | exact d2.2.1 |
          (exfalso; have := d2.1; rw [hkn, h] at this; cases this)
    have hch' : n.children = [] := hch
    rw [hch', List.zip_nil_left, List.foldl_nil, e.1, ← hRj _ hk, List.set_getElem_self]
    exact ⟨inv, hRl⟩
  · -- an inner node: `Δ` merged in, then the children's entries
    push Not at hkl
    obtain ⟨delta, hdelta, h1, h2⟩ := hinner r hr hkl.1 hkl.2.1 hkl.2.2
    simp only [heps] at h1 h2
    set get : ℕ → OnlineAnalyzerNode ℝ A := fun c => (F[c - 1]?.getD n).toRealNode with hgetd
    -- an inner node has children
    have hchne : n.toRealNode.children ≠ [] := by
      cases hψ : ψ k <;> rw [hψ] at d2 <;> simp only [OnlineReachSetAnalyzer.IsNodeOf] at d2
      · exfalso; have := d2.1; rw [hkn] at this; exact hkl.1 this
      · exfalso; have := d2.1; rw [hkn] at this; exact hkl.2.1 this
      · exfalso; have := d2.1; rw [hkn] at this; exact hkl.2.2 this
      all_goals (obtain ⟨-, h⟩ := d2; first | (obtain ⟨c, hc, -⟩ := h; rw [hc]; simp) |
        (obtain ⟨c, c', hc, -⟩ := h; rw [hc]; simp) |
            (obtain ⟨-, c, c', hc, -⟩ := h; rw [hc]; simp))
    -- the children read as reals are valid and kept by their semantics
    have hcv : ∀ c ∈ n.children, (get c).signal.IsValid := by
      intro c hc
      simp only [get, hget c hc]
      have := inv.valid (c - 1) (by rw [hRl]; exact (hrange c hc).2)
      rwa [hRj _ (hrange c hc).2] at this
    have hcw : ∀ c ∈ n.children, aux_WRef (sem c) (get c).signal := by
      intro c hc
      simp only [get, hget c hc]
      have := inv.wsound (c - 1) (by rw [hRl]; exact (hrange c hc).2)
      rwa [hRj _ (hrange c hc).2, show c - 1 + 1 = c by have := (hrange c hc).1; omega] at this
    -- the exact `Δ` on them, which the float one does not contradict
    obtain ⟨Δ, hΔ, -, hΔw⟩ := aux_combine_wref ψ sig sem k n.toRealNode get d2
      (hsem k hk1 (by omega)).1
      (fun c hc => hsem c (hrange c hc).1 (by have := (hrange c hc).2; omega)) hcv hchne
    have hcsR : cs.map OnlineAnalyzerNode.toRealNode = n.toRealNode.children.map get := by
      rw [hcs', List.map_map]; rfl
    have hchv : ∀ c ∈ cs, (c.signal.mapTime toReal).IsValid := by
      intro c hc
      rw [hcs'] at hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      exact hcv c0 hc0
    have hsound := OnlineAnalyzerNode.combineFloat_sound n cs hchv delta hdelta Δ
      (by rw [hcsR]; exact hΔ)
    have hdv := aux_combineFloat_valid n cs hchv delta hdelta
    have hdw : aux_WRef (sem k) (delta.mapTime toReal) := fun t ht =>
      ⟨fun e => ((hΔw hcw) t ht).1 ((hsound t ht).1 e),
       fun e => ((hΔw hcw) t ht).2 ((hsound t ht).2 e)⟩
    -- the node: its signal merged with the float `Δ`
    have hnv : n.toRealNode.signal.IsValid := by
      have := inv.valid (k - 1) (by rw [hRl]; exact hk); rwa [hRj _ hk] at this
    have hnw : aux_WRef (sem k) n.toRealNode.signal := by
      have := inv.wsound (k - 1) (by rw [hRl]; exact hk); rwa [hRj _ hk, hkk] at this
    have hm : aux_Upd sem (k - 1) n.toRealNode r.1.toRealNode := by
      rw [h1]
      refine ⟨rfl, rfl, rfl, rfl, rfl, (FourValuedSignal.merge_spec _ _ hnv hdv).1, ?_⟩
      show aux_WRef (sem (k - 1 + 1)) _
      rw [hkk]
      exact aux_wref_merge hnv hdv hnw hdw
    -- the children: `setPropagated` of their old nodes
    have hrel : List.Forall₂ (fun c y => ∀ h : c - 1 < F.length,
        aux_Upd sem (c - 1) F[c - 1].toRealNode y) n.children
        (r.2.map OnlineAnalyzerNode.toRealNode) := by
      rw [List.forall₂_map_right_iff]
      refine (aux_forall₂_comp hF h2).imp fun c c' ⟨b, hb, hset⟩ h => ?_
      have e : F[c - 1] = b := (List.getElem?_eq_some_iff.1 hb).2
      rw [e]
      have hbv : b.toRealNode.signal.IsValid := by
        have := inv.valid (c - 1) (by rw [hRl]; exact h); rwa [hRj _ h, e] at this
      have hbw : aux_WRef (sem (c - 1 + 1)) b.toRealNode.signal := by
        have := inv.wsound (c - 1) (by rw [hRl]; exact h); rwa [hRj _ h, e] at this
      exact aux_upd_setPropagated sem (c - 1) _ _ _ _ hbv hbw hset
    -- the new list position by position
    obtain ⟨hl, hpos⟩ := aux_foldl_set _ n.children _ hrel (R.set (k - 1) r.1.toRealNode)
      (fun c hc => ⟨(hrange c hc).1, by simp [hRl, (hrange c hc).2]⟩)
    simp only [List.length_set] at hl hpos
    refine ⟨aux_finv_of_upd ψ sem R _ inv (by rw [hl]) fun j h h' => ?_, by rw [hl, hRl]⟩
    have hjF : j < F.length := by rwa [hRl] at h
    by_cases hj : j + 1 ∈ n.children
    · obtain ⟨b, hb, hrb⟩ := (hpos j h).1 hj
      have e : ((n.children.zip (r.2.map OnlineAnalyzerNode.toRealNode)).foldl
          (fun ns p => ns.set (p.1 - 1) p.2) (R.set (k - 1) r.1.toRealNode))[j] = b :=
        (List.getElem?_eq_some_iff.1 hb).2
      rw [e, hRj _ hjF]
      have := hrb (by simpa using hjF)
      simpa using this
    · -- not a child: the node itself, or untouched
      have e := (hpos j h).2 hj
      have e' : ((n.children.zip (r.2.map OnlineAnalyzerNode.toRealNode)).foldl
          (fun ns p => ns.set (p.1 - 1) p.2) (R.set (k - 1) r.1.toRealNode))[j] =
          (R.set (k - 1) r.1.toRealNode)[j]'(by simpa using h) := by
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, e]
      rw [e', List.getElem_set]
      split_ifs with hjk
      · subst hjk; rw [hRj _ hk]; exact hm
      · rw [hRj _ hjF]
        have hv := inv.valid j h; have hw := inv.wsound j h
        rw [hRj _ hjF] at hv hw
        exact aux_upd_refl sem j _ hv hw

end prop2


section prop3
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {S : ℕ → Type} {d : ℕ}

/-- Propagating each node of a list in turn keeps the invariant. -/
private theorem aux_ffold (eps : 𝕋) (heps : toReal eps = 0)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (sem : ℕ → FourValuedSignal ℝ) (fuel : ℕ)
    (ih : ∀ idx (F : List (OnlineAnalyzerNode 𝕋 (AtomicProposition S d))) flags res,
      (∀ i, 1 ≤ i → i ≤ F.length → (ψ i).sat sig = some (sem i) ∧ (sem i).IsValid) →
      aux_FInv ψ sem (F.map OnlineAnalyzerNode.toRealNode) → 1 ≤ idx →
      OnlineReachSetAnalyzer.propagateRecFloat eps .empty fuel idx (F, flags) = some res →
      aux_FInv ψ sem (res.1.map OnlineAnalyzerNode.toRealNode) ∧ res.1.length = F.length) :
    ∀ (L : List ℕ) (F : List (OnlineAnalyzerNode 𝕋 (AtomicProposition S d))) flags res,
      (∀ i, 1 ≤ i → i ≤ F.length → (ψ i).sat sig = some (sem i) ∧ (sem i).IsValid) →
      aux_FInv ψ sem (F.map OnlineAnalyzerNode.toRealNode) → (∀ c ∈ L, 1 ≤ c) →
      L.foldlM (fun st c => OnlineReachSetAnalyzer.propagateRecFloat eps .empty fuel c st)
        (F, flags) = some res →
      aux_FInv ψ sem (res.1.map OnlineAnalyzerNode.toRealNode) ∧ res.1.length = F.length
  | [], F, flags, res, _, inv, _, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨inv, rfl⟩
  | c :: L, F, flags, res, hsem, inv, hL, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.1 h
    -- the head, then the rest from its state
    obtain ⟨i1, i2⟩ := ih c F flags st hsem inv (hL c (by simp)) hst
    obtain ⟨j1, j2⟩ := aux_ffold eps heps ψ sig sem fuel ih L st.1 st.2 res
      (by rw [i2]; exact hsem) i1 (fun c' hc' => hL c' (by simp [hc'])) h
    exact ⟨j1, by rw [j2, i2]⟩

/-- `propagateRecFloat` keeps the invariant. -/
private theorem aux_frec (eps : 𝕋) (heps : toReal eps = 0)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (sem : ℕ → FourValuedSignal ℝ) :
    ∀ fuel idx (F : List (OnlineAnalyzerNode 𝕋 (AtomicProposition S d))) flags res,
      (∀ i, 1 ≤ i → i ≤ F.length → (ψ i).sat sig = some (sem i) ∧ (sem i).IsValid) →
      aux_FInv ψ sem (F.map OnlineAnalyzerNode.toRealNode) → 1 ≤ idx →
      OnlineReachSetAnalyzer.propagateRecFloat eps .empty fuel idx (F, flags) = some res →
      aux_FInv ψ sem (res.1.map OnlineAnalyzerNode.toRealNode) ∧ res.1.length = F.length
  | 0, _, _, _, _, _, _, _, h => by simp [OnlineReachSetAnalyzer.propagateRecFloat] at h
  | fuel + 1, idx, F, flags, res, hsem, inv, hidx, h => by
    simp only [OnlineReachSetAnalyzer.propagateRecFloat] at h
    obtain ⟨node, hnode, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨node2, hnode2, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    -- the children of the node, each propagated first
    have hk : idx - 1 < F.length := (List.getElem?_eq_some_iff.1 hnode).1
    have hnode' : F[idx - 1] = node := (List.getElem?_eq_some_iff.1 hnode).2
    have hdag := (inv.dag (idx - 1) (by simpa using hk)).2.2
    simp only [List.getElem_map, hnode'] at hdag
    obtain ⟨i1, i2⟩ := aux_ffold eps heps ψ sig sem fuel
      (fun idx F flags res => aux_frec eps heps ψ sig sem fuel idx F flags res) _ F flags st
      hsem inv (fun c hc => by
        simp only [List.mem_mergeSort, List.mem_eraseDups, List.mem_filter] at hc
        exact (hdag c hc.1).1) hst
    -- the step at the node itself
    have hk2 : idx - 1 < st.1.length := by rw [i2]; exact hk
    have hnode2' : st.1[idx - 1] = node2 := (List.getElem?_eq_some_iff.1 hnode2).2
    rw [← hnode2'] at hcs hr
    obtain ⟨s1, s2⟩ := aux_fstep eps heps ψ sig sem st.1 (by rw [i2]; exact hsem) i1 idx hidx
      hk2 cs hcs r hr
    rw [← hnode2']
    exact ⟨s1, by rw [s2, i2]⟩

/-- `propagateFloat` keeps the invariant. -/
private theorem aux_fprop (eps : 𝕋) (heps : toReal eps = 0)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (sem : ℕ → FourValuedSignal ℝ)
    (obj obj' : OnlineReachSetAnalyzer 𝕋 S d)
    (hsem : ∀ i, 1 ≤ i → i ≤ obj.nodes.length → (ψ i).sat sig = some (sem i) ∧ (sem i).IsValid)
    (inv : aux_FInv ψ sem (obj.nodes.map OnlineAnalyzerNode.toRealNode))
    (h : obj.propagateFloat eps .empty = some obj') : -- --- CONCL ---
    aux_FInv ψ sem (obj'.nodes.map OnlineAnalyzerNode.toRealNode) ∧
      obj'.nodes.length = obj.nodes.length := by -- --- PROOF ---
  unfold OnlineReachSetAnalyzer.propagateFloat at h
  obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.1 h
  exact aux_frec eps heps ψ sig sem _ 1 obj.nodes _ st hsem inv le_rfl hst

end prop3


section obs
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] [Scalar 𝕋]
  [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S]
  [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)]

/-- The atom signals after observing `set` on `I`: `â(set)` on `I`, the old value elsewhere. -/
private noncomputable def aux_observeAtoms (sig : AtomicProposition S d → FourValuedSignal ℝ)
    (set : S d) (I : STLInterval ℝ) (loc : ℕ) : AtomicProposition S d → FourValuedSignal ℝ :=
  fun a =>
    match OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc with
    | some v => (sig a).set I (FourValued.fromKleene v)
    | none => sig a

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- The semantics of node `i`. -/
private noncomputable def aux_sem (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (i : ℕ) : FourValuedSignal ℝ :=
  ((ψ i).sat sig).getD (FourValuedSignal.uniformSignal .ii)

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- The semantics of node `i` exists and is valid. -/
private theorem aux_sem_spec (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (hv : ∀ a, (sig a).IsValid) (i : ℕ) :
    (ψ i).sat sig = some (aux_sem ψ sig i) ∧ (aux_sem ψ sig i).IsValid := by
  obtain ⟨s, hs, hsv⟩ := (ψ i).sat_spec sig hv
  exact ⟨by simp [aux_sem, hs], by simpa [aux_sem, hs] using hsv⟩


/-- The float leaves observing read as reals are the exact leaves observing. -/
private theorem aux_leaves_toReal (eps : 𝕋) (heps : toReal eps = 0) (set : S d)
    (I : STLInterval 𝕋) (loc : ℕ) :
    ∀ (L : List ℕ) (cur res : List (OnlineAnalyzerNode 𝕋 (AtomicProposition S d))),
      L.foldlM (fun ns l => OnlineReachSetAnalyzer.updateNode ns l fun n =>
        OnlineAnalyzerNode.observeSetFloat eps n set I loc false) cur = some res →
      L.foldlM (fun ns l => OnlineReachSetAnalyzer.updateNode ns l fun n =>
        OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) 0 n set I.toRealInterval loc false)
        (cur.map OnlineAnalyzerNode.toRealNode) = some (res.map OnlineAnalyzerNode.toRealNode)
  | [], cur, res, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h ⊢
    rw [h]
  | l :: L, cur, res, h => by
    simp only [List.foldlM_cons] at h ⊢
    obtain ⟨cur', hcur', h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hl0, x, x', hx, hx', rfl⟩ :=
      (OnlineReachSetAnalyzer.updateNode_eq_some_iff cur l _ cur').1 hcur'
    have e := OnlineAnalyzerNode.observeSetFloat_toRealNode eps x set I loc false
    rw [hx', Option.map_some, heps] at e
    have hup : OnlineReachSetAnalyzer.updateNode (cur.map OnlineAnalyzerNode.toRealNode) l
        (fun n => OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) 0 n set I.toRealInterval loc false) =
        some ((cur.set (l - 1) x').map OnlineAnalyzerNode.toRealNode) := by -- one update
      rw [OnlineReachSetAnalyzer.updateNode_eq_some_iff]
      exact ⟨hl0, x.toRealNode, x'.toRealNode, by simp [hx], e.symm, by rw [List.map_set]⟩
    rw [hup]
    exact aux_leaves_toReal eps heps set I loc L _ res h

/-- One float observation on new times keeps the invariant for the observed atom signals. -/
private theorem aux_fobserve_step (eps : 𝕋) (heps : toReal eps = 0)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (obj obj' : OnlineReachSetAnalyzer 𝕋 S d)
    (set : S d) (I : STLInterval 𝕋) (loc : ℕ) (hsigv : ∀ a, (sig a).IsValid)
    (inv : aux_FInv ψ (aux_sem ψ sig) (obj.nodes.map OnlineAnalyzerNode.toRealNode))
    (hI : I ≠ .empty)
    (hdisj : ∀ a t, 0 ≤ t → t ∈ I.toRealInterval.set → (sig a).at t = .ii)
    (h : obj.observeSetFloat eps set I loc = some obj') : -- --- CONCL ---
    aux_FInv ψ (aux_sem ψ (aux_observeAtoms (𝕋 := 𝕋) sig set I.toRealInterval loc))
      (obj'.nodes.map OnlineAnalyzerNode.toRealNode) ∧ obj'.nodes.length = obj.nodes.length
    := by -- --- PROOF ---
  set sig' := aux_observeAtoms (𝕋 := 𝕋) sig set I.toRealInterval loc with hsig'
  -- the new atom signals are valid and refine the old ones
  have hv' : ∀ a, (sig' a).IsValid := by
    intro a; simp only [sig']; unfold aux_observeAtoms; split
    · exact (FourValuedSignal.set_spec _ (hsigv a) _ _).1
    · exact hsigv a
  have hr' : ∀ a, (sig' a).Refines (sig a) := by
    intro a t ht hne
    simp only [sig']; unfold aux_observeAtoms; split
    · rw [((FourValuedSignal.set_spec _ (hsigv a) _ _).2 t ht).2
        (fun hm => hne (hdisj a t ht hm))]
    · rfl
  -- so the semantics refines the old one
  have hsem' : ∀ i, (aux_sem ψ sig' i).Refines (aux_sem ψ sig i) := fun i =>
    (ψ i).sat_refines sig sig' hsigv hv' hr' _ _ (aux_sem_spec ψ sig hsigv i).1
      (aux_sem_spec ψ sig' hv' i).1
  set R := obj.nodes.map OnlineAnalyzerNode.toRealNode with hR
  have hRl : R.length = obj.nodes.length := by simp [R]
  cases I with
  | empty => exact absurd rfl hI
  | nonempty lo up lc rc p1 p2 p3 =>
  -- the observation: the leaves, then the propagation if due
  simp only [OnlineReachSetAnalyzer.observeSetFloat, Option.isSome_none, Option.getD_none] at h
  obtain ⟨nodes1, hn1, hprop⟩ := Option.bind_eq_some_iff.1 h
  set I : STLInterval 𝕋 := .nonempty lo up lc rc p1 p2 p3 with hIdef
  -- the observed leaves, read as reals
  have hn1R := aux_leaves_toReal eps heps set I loc obj.leaves obj.nodes nodes1 hn1
  obtain ⟨hlen1, hobs⟩ := OnlineReachSetAnalyzer.observeLeaves_spec (𝕋 := 𝕋) R set I.toRealInterval
    loc inv.valid obj.leaves (nodes1.map OnlineAnalyzerNode.toRealNode) hn1R
  -- the invariant after the leaves observed
  have inv1 : aux_FInv ψ (aux_sem ψ sig') (nodes1.map OnlineAnalyzerNode.toRealNode) := by
    refine aux_finv_of_upd ψ _ R _ ?_ hlen1 fun j h h1 => ?_
    · exact ⟨inv.dag, inv.valid, fun j h => aux_wref_trans (hsem' (j + 1)) (inv.wsound j h)⟩
    obtain ⟨h', q1, q2⟩ := hobs j h
    by_cases hp : R[j].kind = .ap ∧ j + 1 ∈ obj.leaves
    · obtain ⟨a, val, ha, hval, e, ev, et⟩ := q2 hp
      obtain ⟨-, hs, -⟩ := inv.dag j h
      have hψ : ∃ l, ψ (j + 1) = .ap l a := by
        cases hψ : ψ (j + 1) <;> rw [hψ] at hs <;> simp only [OnlineReachSetAnalyzer.IsNodeOf] at hs
        case ap l a' => rw [hs.2.2] at ha; cases ha; exact ⟨_, rfl⟩
        all_goals (exfalso; have hk := hs.1; rw [hk] at hp; cases hp.1)
      obtain ⟨l, hψ⟩ := hψ
      -- the observed atom's node: its formula is the atom
      have hsj : aux_sem ψ sig (j + 1) = sig a := by
        simp [aux_sem, hψ, OnlineReachSetAnalyzer.Formula.sat]
      have hsj' : aux_sem ψ sig' (j + 1) =
          (sig a).set I.toRealInterval (FourValued.fromKleene val) := by
        simp [aux_sem, hψ, OnlineReachSetAnalyzer.Formula.sat, sig', aux_observeAtoms, hval]; rfl
      obtain ⟨-, hst⟩ := FourValuedSignal.set_spec (sig a) (hsigv a) I.toRealInterval
        (FourValued.fromKleene val)
      have hw := inv.wsound j h
      rw [hsj] at hw
      have e' : (nodes1.map OnlineAnalyzerNode.toRealNode)[j] =
          { R[j] with signal := (nodes1.map OnlineAnalyzerNode.toRealNode)[j].signal } := e
      refine ⟨by rw [e'], by rw [e'], by rw [e'], by rw [e'], by rw [e'], ev, fun t ht => ?_⟩
      rw [hsj', et t ht]
      split_ifs with hIt
      · rw [(hst t ht).1 hIt]; exact ⟨id, id⟩
      · rw [(hst t ht).2 hIt]; exact hw t ht
    · -- an unobserved node is unchanged; the semantics only refines
      rw [q1 hp]
      exact aux_upd_refl _ j _ (inv.valid j h) (aux_wref_trans (hsem' (j + 1)) (inv.wsound j h))
  have hlenN : nodes1.length = obj.nodes.length := by
    have := hlen1; simp only [List.length_map] at this; rw [this, hRl]
  -- then the propagation, if due
  split_ifs at hprop
  · obtain ⟨p1, p2⟩ := aux_fprop eps heps ψ sig' (aux_sem ψ sig') _ obj'
      (fun i _ _ => aux_sem_spec ψ sig' hv' i) inv1 hprop
    exact ⟨p1, by rw [p2]; exact hlenN⟩
  · cases hprop
    exact ⟨inv1, hlenN⟩

/-- A float run on observations at new, pairwise disjoint times keeps the invariant. -/
private theorem aux_frun (eps : 𝕋) (heps : toReal eps = 0)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) :
    ∀ (obs : List (S d × STLInterval 𝕋 × ℕ)) (sig : AtomicProposition S d → FourValuedSignal ℝ)
      (obj obj' : OnlineReachSetAnalyzer 𝕋 S d),
      aux_FInv ψ (aux_sem ψ sig) (obj.nodes.map OnlineAnalyzerNode.toRealNode) →
      (∀ a, (sig a).IsValid) → (∀ o ∈ obs, o.2.1 ≠ .empty) →
      obs.Pairwise (fun o o' => Disjoint o.2.1.toRealInterval.set o'.2.1.toRealInterval.set) →
      (∀ a (t : ℝ), 0 ≤ t → (sig a).at t ≠ .ii → ∀ o ∈ obs, t ∉ o.2.1.toRealInterval.set) →
      obs.foldlM (fun o x => o.observeSetFloat eps x.1 x.2.1 x.2.2) obj = some obj' →
      aux_FInv ψ (aux_sem ψ (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) sig
        (obs.map fun x => (x.1, x.2.1.toRealInterval, x.2.2))))
        (obj'.nodes.map OnlineAnalyzerNode.toRealNode)
  | [], sig, obj, obj', inv, _, _, _, _, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact inv
  | o :: obs, sig, obj, obj', inv, hsigv, hne, hpw, hfresh, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨obj1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    -- the first observation, on times nothing knows yet
    obtain ⟨inv1, -⟩ := aux_fobserve_step eps heps ψ sig obj obj1 o.1 o.2.1 o.2.2 hsigv inv
      (hne o (by simp)) (fun a t ht hI => by
        by_contra hc; exact hfresh a t ht hc o (by simp) hI) h1
    have hpw' := List.pairwise_cons.1 hpw
    obtain ⟨hv1, hii⟩ := OnlineReachSetAnalyzer.observeAtoms_spec (𝕋 := 𝕋)
      [(o.1, o.2.1.toRealInterval, o.2.2)] sig hsigv
    -- the rest, on times the first observation left unknown
    exact aux_frun eps heps ψ obs _ obj1 obj' inv1 hv1 (fun o' ho' => hne o' (by simp [ho'])) hpw'.2
      (fun a t ht hnii o' ho' hmem => by
        rcases hii a t ht hnii with h' | ⟨o'', ho'', ht''⟩
        · exact hfresh a t ht h' o' (by simp [ho']) hmem
        · simp only [List.mem_singleton] at ho''; subst ho''
          exact Set.disjoint_left.1 (hpw'.1 o' ho') ht'' hmem) h


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeSetFloat_sound (eps : 𝕋) (heps : toReal eps = 0)
    (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hlabel : ∀ l x y, (OnlineReachSetAnalyzer.Formula.ap l x).IsSub φ →
      (OnlineReachSetAnalyzer.Formula.ap l y).IsSub φ → x = y)
    (dp : Bool) (obs : List (S d × STLInterval 𝕋 × ℕ)) (hne : obs ≠ [])
    (hI : ∀ o ∈ obs, o.2.1 ≠ .empty)
    (hdisj : obs.Pairwise fun o o' => Disjoint o.2.1.toRealInterval.set
        o'.2.1.toRealInterval.set) : -- --- CONCL ---
    ∀ objF₀ : OnlineReachSetAnalyzer 𝕋 S d,
      objF₀.toRealAnalyzer ∈ OnlineReachSetAnalyzer.mk? φ 1 dp →
      ∀ objF ∈ obs.foldlM (fun o x => o.observeSetFloat eps x.1 x.2.1 x.2.2) objF₀,
      ∀ obj ∈ (obs.map fun x => (x.1, x.2.1.toRealInterval, x.2.2)).foldlM
          (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) objF₀.toRealAnalyzer,
      ∀ v ∈ objF.getVerdict, (v = .tt ∨ v = .ff) → obj.getVerdict = some v := by -- --- PROOF ---
  intro objF₀ h₀ objF hrunF obj hrun v hv hvc
  -- the observations read as reals meet the hypotheses of `observeSet_correct`
  set obsR := obs.map fun x => (x.1, x.2.1.toRealInterval, x.2.2) with hobsR
  have hIR : ∀ o ∈ obsR, o.2.1 ≠ .empty := by
    intro o ho
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho
    have := hI x hx
    rcases hx2 : x.2.1 with _ | ⟨l, u, lc, rc, hu, hlt, h0⟩
    · exact absurd hx2 this
    · rcases u with _ | u <;> simp [STLInterval.toRealInterval]
  have hdisjR : obsR.Pairwise fun o o' => Disjoint o.2.1.set o'.2.1.set := by
    rw [hobsR, List.pairwise_map]; exact hdisj
  -- the exact run: its root is the semantics
  obtain ⟨s, hs, root, hroot, hrootv⟩ := OnlineReachSetAnalyzer.observeSet_correct (𝕋 := 𝕋) φ
    hlabel dp obsR (by simpa [obsR] using hne) hIR hdisjR _ h₀ obj hrun
  -- the float run: its root is refined by the semantics
  obtain ⟨ψ, hψ1, -, hpos, -, hn⟩ := OnlineReachSetAnalyzer.mk?_nodes_spec φ hlabel 1 dp _ h₀
  -- the initial float analyzer read as reals: the DAG, its initial values the semantics
  set sig₀ : AtomicProposition S d → FourValuedSignal ℝ :=
    fun _ => FourValuedSignal.uniformSignal .ii with hsig₀
  have hsig₀ : ∀ a, (sig₀ a).IsValid := fun _ => (FourValuedSignal.uniformSignal_spec _).1
  have inv₀ : aux_FInv ψ (aux_sem ψ sig₀) (objF₀.nodes.map OnlineAnalyzerNode.toRealNode) := by
    refine ⟨fun j h => ?_, fun j h => (hn j h).2.2.2.1, fun j h => ?_⟩
    · obtain ⟨o1, o2, -, -, -, o11, -⟩ := hn j h
      exact ⟨o1, o2, fun c hc => ⟨(o11 c hc).1, (o11 c hc).2.1⟩⟩
    · obtain ⟨-, o2, -, -, o6, -⟩ := hn j h
      intro t ht
      have e : (OnlineReachSetAnalyzer.toRealAnalyzer objF₀).nodes[j].signal.at t =
          ((objF₀.nodes.map OnlineAnalyzerNode.toRealNode)[j]'h).signal.at t := rfl
      rw [← e, o6 t ht]
      -- the initial value: `True`, `False`, or inconclusive
      cases hψ : ψ (j + 1) <;> rw [hψ] at o2 <;>
        simp only [OnlineReachSetAnalyzer.IsNodeOf] at o2 <;>
        simp only [o2.1, OnlineAnalyzerNode.Kind.initValue]
      · simp only [aux_sem, hψ, OnlineReachSetAnalyzer.Formula.sat, Option.getD_some, sig₀]
        rw [(FourValuedSignal.uniformSignal_spec _).2 t ht]
        exact ⟨fun _ => rfl, fun e => absurd e (by nofun)⟩
      · simp only [aux_sem, hψ, OnlineReachSetAnalyzer.Formula.sat, Option.getD_some, sig₀]
        rw [(FourValuedSignal.uniformSignal_spec _).2 t ht]
        exact ⟨fun e => absurd e (by nofun), fun _ => rfl⟩
      all_goals exact ⟨fun e => absurd e (by nofun), fun e => absurd e (by nofun)⟩
  -- the float run keeps the invariant
  have invF := aux_frun eps heps ψ obs sig₀ objF₀ objF inv₀ hsig₀ hI hdisj
    (fun a t ht hne' => absurd ((FourValuedSignal.uniformSignal_spec _).2 t ht) hne') hrunF
  -- the float verdict is the float root at `0`, read as reals
  rw [← OnlineReachSetAnalyzer.getVerdict_toRealAnalyzer] at hv
  simp only [OnlineReachSetAnalyzer.getVerdict, OnlineReachSetAnalyzer.toRealAnalyzer,
    Option.mem_def, Option.map_eq_some_iff] at hv
  obtain ⟨rootF, hrootF, hvF⟩ := hv
  have h0 : 0 < (objF.nodes.map OnlineAnalyzerNode.toRealNode).length :=
    (List.getElem?_eq_some_iff.1 hrootF).1
  have hrF : (objF.nodes.map OnlineAnalyzerNode.toRealNode)[0] = rootF :=
    (List.getElem?_eq_some_iff.1 hrootF).2
  have hw := invF.wsound 0 h0
  rw [hrF] at hw
  -- the root's semantics is that of `φ`, which the exact root equals
  obtain ⟨hsat, -⟩ := aux_sem_spec ψ _
    (OnlineReachSetAnalyzer.observeAtoms_spec (𝕋 := 𝕋) obsR _ hsig₀).1 1
  rw [hψ1, hs] at hsat
  cases hsat
  simp only [OnlineReachSetAnalyzer.getVerdict, hroot, Option.map_some, Option.some.injEq]
  rw [hrootv 0 le_rfl]
  rcases hvc with rfl | rfl
  · exact (hw 0 le_rfl).1 hvF
  · exact (hw 0 le_rfl).2 hvF

end obs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
