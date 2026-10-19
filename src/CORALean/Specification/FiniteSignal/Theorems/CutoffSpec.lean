module

public import CORALean.Specification.FiniteSignal.Operations.Cutoff
public import CORALean.Specification.FiniteSignal.Theorems.AtEqValueAt
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.ValueAtConsOfGe
public import CORALean.Specification.FiniteSignal.Theorems.MkEqSomeIff
public import CORALean.Specification.FiniteSignal.Theorems.TimeLeDuration

@[expose] public section

/-!
# What `cutoff` computes

For a valid signal and a duration in `[0, duration]`, `cutoff` returns a valid signal of that
duration which agrees with the signal before the new end. At the new end it has the value of the
cell ending there: the signal's own value if `dur` is no breakpoint, otherwise the value of the
breakpoint at `dur` (not the next cell's).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The breakpoints cut at `d`: those before `d`, then `d` with the value of the next. -/
def aux_cutPairs {T V : Type} [LinearOrder T] : List (T × V) → T → List (T × V)
  | [], _ => []
  | (b, v) :: rest, d => if b < d then (b, v) :: aux_cutPairs rest d else [(d, v)]

/-- The index form of `cutoff` is the cut of the breakpoints. -/
theorem aux_cut_zip {T V : Type} [LinearOrder T] (d : T) : -- --- CONCL ---
    ∀ (time : List T) (value : List V), time.length = value.length → (∃ x ∈ time, d ≤ x) →
      (time.take (time.takeWhile (· < d)).length ++ [d]).zip
        (value.take ((time.takeWhile (· < d)).length + 1)) = aux_cutPairs (time.zip value) d ∧
      (time.take (time.takeWhile (· < d)).length ++ [d]).length =
        (value.take ((time.takeWhile (· < d)).length + 1)).length
  | [], _, _, ⟨x, hx, _⟩ => by simp at hx
  | _ :: _, [], h, _ => by simp at h
  | b :: ts, v :: vs, h, ⟨x, hx, hdx⟩ => by
    by_cases hb : b < d
    · have hts : ∃ y ∈ ts, d ≤ y := by -- --- PROOF ---
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hdx (not_le.mpr hb)
        · exact ⟨x, hx, hdx⟩
      -- unpack the facts from the previous steps
      obtain ⟨ih1, ih2⟩ := aux_cut_zip d ts vs (by simpa using h) hts
      simp only [List.takeWhile_cons, hb, decide_true, if_true, List.length_cons,
        List.take_succ_cons, List.cons_append, List.zip_cons_cons, aux_cutPairs, ih1, ih2,
        and_self]
    · simp [hb, aux_cutPairs]

/-- The cut breakpoints: valid, ending at `d`, and with the value of the original before `d`. -/
theorem aux_cut_props {T V : Type} [LinearOrder T] (d : T) : -- --- CONCL ---
    ∀ (L : List (T × V)), L ≠ [] → (L.map Prod.fst).Pairwise (· < ·) → (∃ p ∈ L, d ≤ p.1) →
      aux_cutPairs L d ≠ [] ∧ ((aux_cutPairs L d).map Prod.fst).Pairwise (· < ·) ∧
      (∀ p ∈ aux_cutPairs L d, p.1 ≤ d) ∧ (∃ p ∈ aux_cutPairs L d, p.1 = d) ∧
      ((aux_cutPairs L d).map Prod.snd <+: L.map Prod.snd) ∧
      (∀ p ∈ aux_cutPairs L d, p.1 = d ∨ p.1 ∈ L.map Prod.fst) ∧
      (∀ t, t < d → FiniteSignal.valueAt (aux_cutPairs L d) t = FiniteSignal.valueAt L t) ∧
      (∀ p ∈ L, p.1 = d → FiniteSignal.valueAt (aux_cutPairs L d) d = some p.2) ∧
      ((∀ p ∈ L, p.1 ≠ d) → FiniteSignal.valueAt (aux_cutPairs L d) d =
        FiniteSignal.valueAt L d)
  | [], h, _, _ => absurd rfl h
  | (b, v) :: rest, _, hs, ⟨q, hq, hdq⟩ => by
    rw [List.map_cons, List.pairwise_cons] at hs
    by_cases hb : b < d
    · -- the first breakpoint is before `d`
      -- the fact `hrest`
      have hrest : rest ≠ [] := by -- --- PROOF ---
        rintro rfl
        simp at hq; subst hq; exact absurd hdq (not_le.mpr hb)
      have hq' : ∃ p ∈ rest, d ≤ p.1 := by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact absurd hdq (not_le.mpr hb)
        · exact ⟨q, hq, hdq⟩
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := aux_cut_props d rest hrest hs.2 hq'
      have hcut : aux_cutPairs ((b, v) :: rest) d = (b, v) :: aux_cutPairs rest d := by
        simp [aux_cutPairs, hb]
      obtain ⟨w, ws, hw⟩ := List.exists_cons_of_ne_nil c1
      rw [hcut]
      refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.pairwise_cons]
        -- prove the parts of the goal
        refine ⟨fun x hx => ?_, c2⟩
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
        rcases c6 z hz with h | h
        · exact h ▸ hb
        · exact hs.1 _ h
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hb.le
        · exact c3 p hp
      · obtain ⟨p, hp, hpd⟩ := c4; exact ⟨p, List.mem_cons_of_mem _ hp, hpd⟩
      · simpa using (List.prefix_cons_inj v).mpr c5
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact Or.inr (by simp)
        -- split into the cases
        · rcases c6 p hp with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro t ht
        by_cases htb : t < b
        · rw [FiniteSignal.valueAt_cons_of_lt _ _ t htb, FiniteSignal.valueAt_cons_of_lt _ _ t htb]
        · rw [FiniteSignal.valueAt_cons_of_ge _ _ t htb c1,
            FiniteSignal.valueAt_cons_of_ge _ _ t htb hrest]
          exact c7 t ht
      · intro p hp hpd
        have hbd : ¬ d < b := not_lt.mpr hb.le
        rw [FiniteSignal.valueAt_cons_of_ge _ _ d hbd c1]
        rcases List.mem_cons.mp hp with rfl | hp
        · exact absurd hpd (ne_of_lt hb)
        · exact c8 p hp hpd
      -- introduce the variables
      · intro hne
        have hbd : ¬ d < b := not_lt.mpr hb.le
        rw [FiniteSignal.valueAt_cons_of_ge _ _ d hbd c1,
          FiniteSignal.valueAt_cons_of_ge _ _ d hbd hrest]
        exact c9 (fun p hp => hne p (List.mem_cons_of_mem _ hp))
    · -- the first breakpoint is at or after `d`: the cut stops there
      have hcut : aux_cutPairs ((b, v) :: rest) d = [(d, v)] := by simp [aux_cutPairs, hb]
      rw [hcut]
      have hbd : d ≤ b := not_lt.mp hb
      refine ⟨by simp, by simp, by simp, ⟨(d, v), by simp, rfl⟩, by simp, by simp, fun t ht => ?_,
        fun p hp hpd => ?_, fun hne => ?_⟩
      · rw [FiniteSignal.valueAt_singleton, FiniteSignal.valueAt_cons_of_lt _ _ t (ht.trans_le hbd)]
      · rw [FiniteSignal.valueAt_singleton]
        rcases List.mem_cons.mp hp with rfl | hp
        · rfl
        -- conclude
        · exact absurd (hs.1 p.1 (List.mem_map_of_mem hp)) (not_lt.mpr (hpd ▸ hbd))
      · rw [FiniteSignal.valueAt_singleton,
          FiniteSignal.valueAt_cons_of_lt _ _ d
            (lt_of_le_of_ne hbd (fun h => hne _ (by simp) h.symm))]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.cutoff?_spec {T V : Type} [LinearOrder T] [Zero T] [DecidableEq V]
    (s : FiniteSignal T V) (hs : s.IsValid) (dur : T) (h0 : 0 ≤ dur)
    (h1 : dur ≤ s.duration) : -- --- CONCL ---
    ∃ r, s.cutoff? dur = some r ∧ r.IsValid ∧ r.duration = dur ∧
      (∀ t, t < dur → r.at? t = s.at? t) ∧
      (dur ∉ s.time → r.at? dur = s.at? dur) ∧
      (∀ i : ℕ, s.time[i]? = some dur → r.at? dur = s.value[i]?) := by -- --- PROOF ---
  obtain ⟨hmem, hle⟩ := FiniteSignal.time_le_duration s hs
  obtain ⟨hne, hl, hp, hch, hnn⟩ := hs
  -- the breakpoints of the signal
  have hmap : s.pairs.map Prod.fst = s.time := by simp [FiniteSignal.pairs, List.map_fst_zip, hl]
  have hmaps : s.pairs.map Prod.snd = s.value := by simp [FiniteSignal.pairs, List.map_snd_zip, hl]
  have hLne : s.pairs ≠ [] := fun h => hne (by rw [← hmap, h]; rfl)
  have hex : ∃ p ∈ s.pairs, dur ≤ p.1 := by
    obtain ⟨p, hpm, hpe⟩ := List.mem_map.mp (hmap ▸ hmem : s.duration ∈ s.pairs.map Prod.fst)
    exact ⟨p, hpm, hpe ▸ h1⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    aux_cut_props dur s.pairs hLne (hmap ▸ hp) hex
  -- the index form of the cut is the cut of the breakpoints
  obtain ⟨z1, z2⟩ := aux_cut_zip dur s.time s.value hl ⟨s.duration, hmem, h1⟩
  obtain ⟨T', V', hT, hV⟩ : ∃ T' V', T' = s.time.take (s.time.takeWhile (· < dur)).length ++ [dur]
      ∧ V' = s.value.take ((s.time.takeWhile (· < dur)).length + 1) := ⟨_, _, rfl, rfl⟩
  rw [← hT, ← hV] at z1 z2
  have hcut : s.cutoff? dur = FiniteSignal.mk? T' V' := by
    unfold FiniteSignal.cutoff?
    rw [if_neg (not_lt.mpr h1)]
    subst hT hV
    rfl
  have hC : T'.zip V' = aux_cutPairs s.pairs dur := z1
  have hT' : T' = (aux_cutPairs s.pairs dur).map Prod.fst := by
    rw [← hC, List.map_fst_zip z2.le]
  have hV' : V' = (aux_cutPairs s.pairs dur).map Prod.snd := by
    rw [← hC, List.map_snd_zip z2.ge]
  -- the cut signal is valid
  have hv : (⟨T', V'⟩ : FiniteSignal T V).IsValid := by
    refine ⟨?_, z2, hT' ▸ c2, ?_, fun t ht => ?_⟩
    · rw [hT']; exact fun h => c1 (List.map_eq_nil_iff.mp h)
    · rw [hV']
      exact (hch.infix (hmaps ▸ c5).isInfix : _)
    · rw [hT'] at ht
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
      rcases c6 q hq with h | h
      · exact h ▸ h0
      · exact hnn _ (hmap ▸ h)
  have hmk : s.cutoff? dur = some ⟨T', V'⟩ :=
    hcut.trans ((FiniteSignal.mk?_eq_some_iff _ _ _).mpr ⟨rfl, rfl, hv⟩)
  have hpairs : (⟨T', V'⟩ : FiniteSignal T V).pairs = aux_cutPairs s.pairs dur := hC
  -- the duration is `dur`
  have hdur : (⟨T', V'⟩ : FiniteSignal T V).duration = dur := by
    obtain ⟨hm, hle'⟩ := FiniteSignal.time_le_duration _ hv
    obtain ⟨p, hp', hpd⟩ := c4
    have hdm : dur ∈ T' := by rw [hT']; exact List.mem_map.mpr ⟨p, hp', hpd⟩
    refine le_antisymm ?_ (hle' _ hdm)
    have hm' : (⟨T', V'⟩ : FiniteSignal T V).duration ∈ T' := hm
    generalize (⟨T', V'⟩ : FiniteSignal T V).duration = dd at hm' ⊢
    rw [hT'] at hm'
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm'
    exact hqe ▸ c3 q hq
  refine ⟨_, hmk, hv, hdur, fun t ht => ?_, fun hnot => ?_, fun i hi => ?_⟩
  · rw [FiniteSignal.at?_eq_valueAt _ z2 t, FiniteSignal.at?_eq_valueAt s hl t, hpairs, hdur]
    by_cases ht0 : 0 ≤ t
    · rw [if_pos ⟨ht0, ht.le⟩, if_pos ⟨ht0, ht.le.trans h1⟩]; exact c7 t ht
    -- rewrite and simplify
    · rw [if_neg (fun h => ht0 h.1), if_neg (fun h => ht0 h.1)]
  · rw [FiniteSignal.at?_eq_valueAt _ z2 dur, FiniteSignal.at?_eq_valueAt s hl dur, hpairs, hdur,
      if_pos ⟨h0, le_rfl⟩, if_pos ⟨h0, h1⟩]
    exact c9 fun p hp heq => hnot (heq ▸ hmap ▸ List.mem_map_of_mem hp)
  · have hlt : i < s.value.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega
    have hpm : (dur, s.value[i]) ∈ s.pairs := by
      refine List.mem_iff_getElem?.mpr ⟨i, ?_⟩
      exact List.getElem?_zip_eq_some.mpr ⟨hi, List.getElem?_eq_getElem hlt⟩
    rw [FiniteSignal.at?_eq_valueAt _ z2 dur, hpairs, hdur, if_pos ⟨h0, le_rfl⟩,
      c8 _ hpm rfl, List.getElem?_eq_getElem hlt]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
