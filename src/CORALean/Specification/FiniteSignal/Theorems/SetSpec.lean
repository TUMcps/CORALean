module

public import CORALean.Specification.FiniteSignal.Operations.Set
public import CORALean.Specification.FiniteSignal.Theorems.AtEqValueAt
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.MkEqSomeIff
public import CORALean.Specification.FiniteSignal.Theorems.PairsOfValid
public import CORALean.Specification.FiniteSignal.Theorems.TakeWhileGetElem
public import CORALean.Specification.FiniteSignal.Theorems.TimeLeDuration
public import CORALean.Specification.FiniteSignal.Theorems.ValueAtConsOfGe

@[expose] public section

/-!
# What `set` computes

For a valid signal whose first cell is not empty (`time(1) > 0`) and an interval `[lo,hi]` with
`max(lo,0) < min(hi,duration)`, `set` returns a valid signal of the same duration whose value is
`value` on `[lb, ub)` (and at the duration if `ub` is the duration), where `lb = max(lo,0)` and
`ub = min(hi,duration)`, and the signal's own value elsewhere.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A breakpoint of the prefix beyond `t` decides the value, as in the whole list. -/
theorem aux_valueAt_append_lt {V : Type} (P X : List (ℝ × V)) (t : ℝ) (hX : X ≠ [])
    (h : ∃ p ∈ P, t < p.1) :
    FiniteSignal.valueAt (P ++ X) t = FiniteSignal.valueAt P t := by -- --- PROOF ---
  induction P with
  | nil => simp at h
  | cons p P ih =>
    by_cases ht : t < p.1
    · rw [List.cons_append, FiniteSignal.valueAt_cons_of_lt p _ t ht,
        FiniteSignal.valueAt_cons_of_lt p _ t ht]
    · obtain ⟨q, hq, hqt⟩ := h
      have hP : P ≠ [] := by
        rintro rfl
        rcases List.mem_singleton.mp hq with rfl
        exact ht hqt
      have h' : ∃ p' ∈ P, t < p'.1 := by
        -- split into the cases
        rcases List.mem_cons.mp hq with rfl | hq
        · exact absurd hqt ht
        · exact ⟨q, hq, hqt⟩
      rw [List.cons_append, FiniteSignal.valueAt_cons_of_ge p _ t ht (by simp [hX]),
        FiniteSignal.valueAt_cons_of_ge p _ t ht hP, ih h']

/-- If no breakpoint of the prefix is beyond `t`, only the rest decides the value. -/
theorem aux_valueAt_append_ge {V : Type} (P X : List (ℝ × V)) (t : ℝ) (hX : X ≠ [])
    (h : ∀ p ∈ P, p.1 ≤ t) :
    FiniteSignal.valueAt (P ++ X) t = FiniteSignal.valueAt X t := by -- --- PROOF ---
  induction P with
  | nil => rfl
  | cons p P ih =>
    rw [List.cons_append, FiniteSignal.valueAt_cons_of_ge p _ t (not_lt.mpr (h p (by simp)))
      (by simp [hX]), ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- The index form of a splice of the arrays is the splice of the breakpoints. -/
theorem aux_zip_splice {α β : Type} (t : List α) (v : List β) (A B : ℕ) (nT : List α)
    (nV : List β) (h : t.length = v.length) (hn : nT.length = nV.length) :
    (t.take A ++ nT ++ t.drop B).zip (v.take A ++ nV ++ v.drop B) =
      (t.zip v).take A ++ nT.zip nV ++ (t.zip v).drop B := by
  rw [List.zip_append (by simp [List.length_append, hn, h]), List.zip_append (by simp [h])]
  simp only [List.zip, List.take_zipWith, List.drop_zipWith, List.append_assoc]


/-- The last breakpoint of a nonempty prefix is the one before its length. -/
theorem aux_last_take {α : Type} (L : List α) (k : ℕ) (hk0 : 0 < k) (hk : k ≤ L.length) :
    (L.take k).getLast? = L[k - 1]? := by
  rw [List.getLast?_take]
  have : k ≠ 0 := by omega
  simp [this, List.getElem?_eq_getElem (show k - 1 < L.length by omega)]

/-- The prefix `L.take k` of the breakpoints decides the value before `a` if it has a breakpoint
beyond `t`; otherwise the first breakpoint of the rest does. -/
theorem aux_value_prefix {V : Type} (L : List (ℝ × V)) (k : ℕ) (hk : k < L.length) (t : ℝ)
    (X : List (ℝ × V)) (hX : X ≠ []) : -- --- STMT ---
    ((∃ p ∈ L.take k, t < p.1) → FiniteSignal.valueAt (L.take k ++ X) t = FiniteSignal.valueAt L t)
    ∧ ((∀ p ∈ L.take k, p.1 ≤ t) → FiniteSignal.valueAt (L.take k ++ X) t =
        FiniteSignal.valueAt X t ∧
        FiniteSignal.valueAt L t = FiniteSignal.valueAt (L.drop k) t) := by -- --- PROOF ---
  have hd : L.drop k ≠ [] := by simp; omega
  refine ⟨fun h => ?_, fun h => ⟨aux_valueAt_append_ge _ _ t hX h, ?_⟩⟩
  · conv_rhs => rw [← List.take_append_drop k L]
    rw [aux_valueAt_append_lt _ _ t hX h, aux_valueAt_append_lt _ _ t hd h]
  · conv_lhs => rw [← List.take_append_drop k L]
    exact aux_valueAt_append_ge _ _ t hd h

/-- The left part of the result of `set`: valid, ending before `a` with a value other than `value`,
and acting as the signal before `a`. -/
theorem aux_set_left {V : Type} [DecidableEq V] (s : FiniteSignal ℝ V) (hs : s.IsValid)
    (hpos : ∀ b ∈ s.time.head?, 0 < b) (a : ℝ) (ha0 : 0 ≤ a) (value : V) (sI : ℕ)
    (hsI : sI < s.time.length) (hT1 : ∀ i (hi : i < sI), s.time[i]'(by omega) ≤ a)
    (hT2 : a < s.time[sI]) (A : ℕ) (nT : List ℝ) (nV : List V)
    (h : s.aux_setLower a value sI = (A, nT, nV)) : -- --- STMT ---
    A ≤ s.time.length ∧ nT.length = nV.length ∧
      ((s.pairs.take A ++ nT.zip nV).map Prod.fst).Pairwise (· < ·) ∧
      (∀ p ∈ s.pairs.take A ++ nT.zip nV, 0 ≤ p.1 ∧ p.1 ≤ a) ∧
      ((s.pairs.take A ++ nT.zip nV).map Prod.snd).IsChain (· ≠ ·) ∧
      (∀ p ∈ (s.pairs.take A ++ nT.zip nV).getLast?, p.2 ≠ value) ∧
      ∀ t : ℝ, 0 ≤ t → t < a → ∀ W : List (ℝ × V), W ≠ [] →
        (∀ p ∈ W.head?, a < p.1 ∧ p.2 = value) →
        FiniteSignal.valueAt (s.pairs.take A ++ nT.zip nV ++ W) t =
          FiniteSignal.valueAt s.pairs t := by -- --- PROOF ---
  obtain ⟨hne, hl, hp, hch, hnn⟩ := hs
  -- the breakpoints of the signal
  have hlen : s.pairs.length = s.time.length := by simp [FiniteSignal.pairs, hl]
  have hmap : s.pairs.map Prod.fst = s.time := by simp [FiniteSignal.pairs, List.map_fst_zip, hl]
  have hmaps : s.pairs.map Prod.snd = s.value := by simp [FiniteSignal.pairs, List.map_snd_zip, hl]
  have hget : ∀ i (hi : i < s.pairs.length), s.pairs[i] =
      (s.time[i]'(by omega), s.value[i]'(by omega)) := fun i hi => by simp [FiniteSignal.pairs]
  have hsv : s.value[sI]? = some (s.value[sI]'(by omega)) := List.getElem?_eq_getElem _
  -- the breakpoints before `sI` are before `a`, the others after it
  have hmem : ∀ k, k ≤ sI → ∀ p ∈ s.pairs.take k, p.1 ≤ a := fun k hk p hp' => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
    simp only [List.length_take] at hi
    rw [List.getElem_take, hget i (by omega)]
    exact hT1 i (by omega)
  have hmem' : ∀ p ∈ s.pairs.drop sI, a < p.1 := fun p hp' => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
    simp only [List.length_drop] at hi
    have hi' : sI + i < s.pairs.length := by omega
    rw [List.getElem_drop, hget (sI + i) hi']
    have := List.pairwise_iff_getElem.mp hp
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact hT2
    · exact hT2.trans (this sI (sI + i) hsI (by omega) (by omega))
  -- the properties every prefix of the breakpoints has
  have hLs : (s.pairs.map Prod.fst).Pairwise (· < ·) := hmap ▸ hp
  have hLc : (s.pairs.map Prod.snd).IsChain (· ≠ ·) := hmaps ▸ hch
  have hsortk : ∀ k, ((s.pairs.take k).map Prod.fst).Pairwise (· < ·) := fun k => by
    rw [List.map_take]; exact hLs.sublist (List.take_sublist _ _)
  have hchk : ∀ k, ((s.pairs.take k).map Prod.snd).IsChain (· ≠ ·) := fun k => by
    rw [List.map_take]; exact hLc.infix (List.take_prefix k _).isInfix
  have hnnk : ∀ k, ∀ p ∈ s.pairs.take k, 0 ≤ p.1 := fun k p hp' =>
    hnn _ (hmap ▸ List.mem_map_of_mem (List.mem_of_mem_take hp'))
  -- the last value of the prefix before `sI` differs from the value of the cell of `a`
  have hlastv : ∀ k, 0 < k → k ≤ sI → ∀ p ∈ (s.pairs.take k).getLast?,
      some p.2 = s.value[k - 1]? := fun k hk0 hk p hp' => by
    rw [aux_last_take _ k hk0 (by omega)] at hp'
    have hk1 : k - 1 < s.pairs.length := by omega
    rw [List.getElem?_eq_getElem hk1] at hp'
    rw [Option.mem_def, Option.some.injEq] at hp'
    rw [← hp', hget (k - 1) hk1, List.getElem?_eq_getElem (by omega)]
  have hdrop : ∀ k (hk : k < s.pairs.length), s.pairs.drop k =
      (s.time[k]'(by omega), s.value[k]'(by omega)) :: s.pairs.drop (k + 1) := fun k hk => by
    rw [List.drop_eq_getElem_cons hk, hget k hk]
  -- the times are monotone
  have hmono : ∀ i j (hi : i < s.time.length) (hj : j < s.time.length), i ≤ j →
      s.time[i] ≤ s.time[j] := fun i j hi hj hij => by
    rcases hij.lt_or_eq with h' | rfl
    · exact (List.pairwise_iff_getElem.mp hp i j hi hj h').le
    · exact le_rfl
  -- adjacent values differ
  have hadj : ∀ i (hi : i + 1 < s.value.length), s.value[i] ≠ s.value[i + 1] :=
    List.isChain_iff_getElem.mp hch
  have hadj' : ∀ i j (hj : j < s.value.length) (hij : i + 1 = j),
      s.value[i]'(by omega) ≠ s.value[j] := fun i j hj hij => by subst hij; exact hadj i hj
  unfold FiniteSignal.aux_setLower at h
  by_cases c1 : s.value[sI]? ≠ some value ∧ 0 < a
  · rw [if_pos c1] at h
    by_cases c2 : 0 < sI ∧ s.time[sI - 1]? = some a
    · rw [if_pos c2] at h
      have ht1 : s.time[sI - 1]'(by omega) = a := by
        have := c2.2; rwa [List.getElem?_eq_getElem (by omega), Option.some.injEq] at this
      by_cases c3 : s.value[sI - 1]? = some value
      · -- merged with the cell before
        rw [if_pos c3] at h
        -- rewrite and simplify
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hv1 : s.value[sI - 1]'(by omega) = value := by
          rwa [List.getElem?_eq_getElem (by omega), Option.some.injEq] at c3
        simp only [List.zip_nil_left, List.append_nil]
        refine ⟨by omega, rfl, hsortk _, fun p hp' => ⟨hnnk _ p hp', hmem _ (by omega) p hp'⟩,
          hchk _, fun p hp' => ?_, fun t ht0 hta W hW hWh => ?_⟩
        · -- the value before the merged cell differs from it
          rcases Nat.eq_zero_or_pos (sI - 1) with h0 | hpos'
          · rw [h0] at hp'; simp at hp'
          · have := hlastv _ hpos' (by omega) p hp'
            rw [List.getElem?_eq_getElem (by omega)] at this
            have hne' := hadj' (sI - 1 - 1) (sI - 1) (by omega) (by omega)
            intro hpv
            -- rewrite and simplify
            rw [Option.some.injEq] at this
            exact hne' (by rw [← this, hpv, hv1])
        · -- before `a` the cell of `a` is the merged one
          obtain ⟨w, W', rfl⟩ := List.exists_cons_of_ne_nil hW
          obtain ⟨hwa, hwv⟩ := hWh w (by simp)
          have hdw : (s.pairs.drop (sI - 1)).head? = some (a, value) := by
            rw [hdrop (sI - 1) (by omega), List.head?_cons, ht1, hv1]
          by_cases hex : ∃ p ∈ s.pairs.take (sI - 1), t < p.1
          · exact (aux_value_prefix s.pairs (sI - 1) (by omega) t (w :: W') (by simp)).1 hex
          · push Not at hex
            obtain ⟨e1, e2⟩ :=
              (aux_value_prefix s.pairs (sI - 1) (by omega) t (w :: W') (by simp)).2 hex
            rw [e1, e2, hdrop (sI - 1) (by omega), ht1, hv1,
              FiniteSignal.valueAt_cons_of_lt w W' t (hta.trans hwa),
              FiniteSignal.valueAt_cons_of_lt (a, value) _ t hta, hwv]
      · -- the boundary at `a` stays
        -- rewrite and simplify
        rw [if_neg c3] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [List.zip_nil_left, List.append_nil]
        refine ⟨by omega, rfl, hsortk _, fun p hp' => ⟨hnnk _ p hp', hmem _ le_rfl p hp'⟩,
          hchk _, fun p hp' => ?_, fun t ht0 hta W hW hWh => ?_⟩
        · -- the value before `a` differs from `value`
          have := hlastv _ c2.1 le_rfl p hp'
          intro hpv
          exact c3 (by rw [← this, hpv])
        · -- the last breakpoint of the prefix is at `a`, beyond `t`
          have hlt : sI - 1 < (s.pairs.take sI).length := by simp; omega
          have hex : ∃ p ∈ s.pairs.take sI, t < p.1 := by
            refine ⟨(s.pairs.take sI)[sI - 1], List.getElem_mem hlt, ?_⟩
            -- rewrite and simplify
            rw [List.getElem_take, hget (sI - 1) (by omega), ht1]
            exact hta
          exact (aux_value_prefix s.pairs sI (by omega) t W hW).1 hex
    · -- a boundary is added at `a`
      rw [if_neg c2] at h
      rw [hsv] at h
      simp only [Option.toList_some, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [List.zip_cons_cons, List.zip_nil_right]
      -- the breakpoints before `sI` are strictly before `a`
      have hlt : ∀ p ∈ s.pairs.take sI, p.1 < a := fun p hp' => by
        refine lt_of_le_of_ne (hmem _ le_rfl p hp') fun hpa => c2 ⟨?_, ?_⟩
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
          simp only [List.length_take] at hi
          omega
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
          simp only [List.length_take] at hi
          have hi2 : i < sI := by omega
          rw [List.getElem_take, hget i (by omega)] at hpa
          have h1 := hT1 (sI - 1) (by omega)
          have h2 := hmono i (sI - 1) (by omega) (by omega) (by omega)
          rw [List.getElem?_eq_getElem (by omega)]
          simp only [] at hpa
          exact congrArg some (le_antisymm h1 (hpa ▸ h2))
      -- the fact `hvsne`
      have hvsne : s.value[sI]'(by omega) ≠ value := fun hv' =>
        c1.1 (by rw [hsv, hv'])
      refine ⟨by omega, rfl, ?_, fun p hp' => ?_, ?_, fun p hp' => ?_, fun t ht0 hta W hW hWh => ?_⟩
      · -- ordered: the breakpoints before `sI` are before `a`
        rw [List.map_append, List.pairwise_append]
        refine ⟨hsortk _, by simp, fun x hx y hy => ?_⟩
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
        rw [List.map_cons, List.map_nil, List.mem_singleton] at hy
        rw [hy]; exact hlt p hp'
      · -- the times are in `[0, a]`
        rcases List.mem_append.mp hp' with h' | h'
        · exact ⟨hnnk _ p h', hmem _ le_rfl p h'⟩
        · rw [List.mem_singleton] at h'; rw [h']; exact ⟨ha0, le_rfl⟩
      · -- the values alternate
        -- rewrite and simplify
        rw [List.map_append, List.map_cons, List.map_nil, List.isChain_append]
        refine ⟨hchk _, List.isChain_singleton _, fun x hx y hy => ?_⟩
        rw [List.getLast?_map, Option.mem_def, Option.map_eq_some_iff] at hx
        obtain ⟨p, hp', rfl⟩ := hx
        rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        rcases Nat.eq_zero_or_pos sI with h0 | hpos'
        · rw [h0] at hp'; simp at hp'
        · have := hlastv _ hpos' le_rfl p hp'
          rw [List.getElem?_eq_getElem (by omega)] at this
          rw [← hy]
          intro hxy
          rw [Option.some.injEq] at this
          exact hadj' (sI - 1) sI (by omega) (by omega) (by rw [← this, hxy])
      · -- the last value is that of the cell of `a`
        -- rewrite and simplify
        rw [List.getLast?_append, Option.mem_def] at hp'
        simp at hp'
        rw [← hp']; exact hvsne
      · -- before `a` the cell of `a` gives the value
        have key := aux_value_prefix s.pairs sI (by omega) t
          ((a, s.value[sI]'(by omega)) :: W) (by simp)
        rw [List.append_assoc, List.singleton_append]
        by_cases hex : ∃ p ∈ s.pairs.take sI, t < p.1
        · exact key.1 hex
        · push Not at hex
          obtain ⟨e1, e2⟩ := key.2 hex
          rw [e1, e2, hdrop sI (by omega), FiniteSignal.valueAt_cons_of_lt _ _ t hta,
            FiniteSignal.valueAt_cons_of_lt _ _ t (hta.trans hT2)]
  · -- nothing is added at `a`
    -- rewrite and simplify
    rw [if_neg c1] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [List.zip_nil_left, List.append_nil]
    -- either the cell of `a` already has the value, or `a = 0` and nothing precedes it
    have hc : s.value[sI]? = some value ∨ a ≤ 0 := by
      by_cases h1 : s.value[sI]? = some value
      · exact Or.inl h1
      · exact Or.inr (not_lt.mp fun h2 => c1 ⟨h1, h2⟩)
    refine ⟨by omega, rfl, hsortk _, fun p hp' => ⟨hnnk _ p hp', hmem _ le_rfl p hp'⟩, hchk _,
      fun p hp' => ?_, fun t ht0 hta W hW hWh => ?_⟩
    · -- the value before `a` differs from the value of the cell of `a`
      rcases Nat.eq_zero_or_pos sI with h0 | hpos'
      · rw [h0] at hp'; simp at hp'
      · have := hlastv _ hpos' le_rfl p hp'
        rcases hc with hc | hc
        · rw [List.getElem?_eq_getElem (by omega)] at this hc
          rw [Option.some.injEq] at this hc
          exact fun hpv => hadj' (sI - 1) sI (by omega) (by omega) (by rw [← this, hpv, hc])
        · exfalso
          -- the fact `h1`
          have h1 := hT1 0 (by omega)
          have h2 := hpos (s.time[0]'(by omega)) (by simp [List.head?_eq_getElem?])
          linarith
    · -- before `a` the cell of `a` already has the value
      have hvs : s.value[sI]'(by omega) = value := by
        rcases hc with hc | hc
        · rwa [hsv, Option.some.injEq] at hc
        · exfalso; linarith
      obtain ⟨w, W', rfl⟩ := List.exists_cons_of_ne_nil hW
      obtain ⟨hwa, hwv⟩ := hWh w (by simp)
      by_cases hex : ∃ p ∈ s.pairs.take sI, t < p.1
      · exact (aux_value_prefix s.pairs sI (by omega) t (w :: W') (by simp)).1 hex
      · push Not at hex
        obtain ⟨e1, e2⟩ := (aux_value_prefix s.pairs sI (by omega) t (w :: W') (by simp)).2 hex
        -- rewrite and simplify
        rw [e1, e2, hdrop sI (by omega), hvs,
          FiniteSignal.valueAt_cons_of_lt w W' t (hta.trans hwa),
          FiniteSignal.valueAt_cons_of_lt _ _ t (hta.trans hT2), hwv]

/-- The right part of the result of `set`: ordered, ending at the duration, starting with `value`
and acting as the signal from `b` on. -/
theorem aux_set_right {V : Type} [DecidableEq V] (s : FiniteSignal ℝ V) (hs : s.IsValid)
    (b : ℝ) (hb0 : 0 ≤ b) (value : V) (hbD : b ≤ s.duration) (pI : ℕ)
    (hpI : pI ≤ s.time.length) (hP1 : ∀ i (hi : i < pI), s.time[i]'(by omega) ≤ b)
    (hP2 : ∀ (hi : pI < s.time.length), b < s.time[pI]) (U : Prop) [Decidable U]
    (hU : U ↔ (b = s.duration ∨ s.value[pI]? ≠ some value)) : -- --- STMT ---
    ((if U then [(b, value)] else []) ++ s.pairs.drop pI) ≠ [] ∧
    (∀ p ∈ ((if U then [(b, value)] else []) ++ s.pairs.drop pI).head?, b ≤ p.1 ∧ p.2 = value) ∧
    (((if U then [(b, value)] else []) ++ s.pairs.drop pI).map Prod.fst).Pairwise (· < ·) ∧
    (∀ p ∈ (if U then [(b, value)] else []) ++ s.pairs.drop pI, 0 ≤ p.1 ∧ b ≤ p.1) ∧
    (((if U then [(b, value)] else []) ++ s.pairs.drop pI).map Prod.snd).IsChain (· ≠ ·) ∧
    (∃ p ∈ ((if U then [(b, value)] else []) ++ s.pairs.drop pI).getLast?, p.1 = s.duration) ∧
    ∀ t : ℝ, b ≤ t → t ≤ s.duration →
      (b = s.duration → FiniteSignal.valueAt ((if U then [(b, value)] else []) ++
        s.pairs.drop pI) t = some value) ∧
      (b < s.duration → FiniteSignal.valueAt ((if U then [(b, value)] else []) ++
        s.pairs.drop pI) t = FiniteSignal.valueAt s.pairs t) := by -- --- PROOF ---
  -- unpack the facts from the previous steps
  obtain ⟨hmem, hle⟩ := FiniteSignal.time_le_duration s hs
  obtain ⟨hne, hl, hp, hch, hnn⟩ := hs
  -- the breakpoints of the signal
  have hlen : s.pairs.length = s.time.length := by simp [FiniteSignal.pairs, hl]
  have hmap : s.pairs.map Prod.fst = s.time := by simp [FiniteSignal.pairs, List.map_fst_zip, hl]
  have hmaps : s.pairs.map Prod.snd = s.value := by simp [FiniteSignal.pairs, List.map_snd_zip, hl]
  have hget : ∀ i (hi : i < s.pairs.length), s.pairs[i] =
      (s.time[i]'(by omega), s.value[i]'(by omega)) := fun i hi => by simp [FiniteSignal.pairs]
  have hLs : (s.pairs.map Prod.fst).Pairwise (· < ·) := hmap ▸ hp
  have hLc : (s.pairs.map Prod.snd).IsChain (· ≠ ·) := hmaps ▸ hch
  have hdrop : ∀ k (hk : k < s.pairs.length), s.pairs.drop k =
      (s.time[k]'(by omega), s.value[k]'(by omega)) :: s.pairs.drop (k + 1) := fun k hk => by
    rw [List.drop_eq_getElem_cons hk, hget k hk]
  -- the breakpoints from `pI` on are after `b`, ordered, alternating, and nonnegative
  have hbig : ∀ p ∈ s.pairs.drop pI, b < p.1 := fun p hp' => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
    simp only [List.length_drop] at hi
    have hi' : pI + i < s.pairs.length := by omega
    rw [List.getElem_drop, hget (pI + i) hi']
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact hP2 (by omega)
    · exact (hP2 (by omega)).trans
        (List.pairwise_iff_getElem.mp hp pI (pI + i) (by omega) (by omega) (by omega))
  have hsortd : ((s.pairs.drop pI).map Prod.fst).Pairwise (· < ·) := by
    rw [List.map_drop]; exact hLs.sublist (List.drop_sublist _ _)
  have hchd : ((s.pairs.drop pI).map Prod.snd).IsChain (· ≠ ·) := by
    rw [List.map_drop]; exact hLc.infix (List.drop_suffix pI _).isInfix
  have hnnd : ∀ p ∈ s.pairs.drop pI, 0 ≤ p.1 := fun p hp' => (hb0.trans (hbig p hp').le)
  -- the last breakpoint is at the duration
  have hlast : ∃ p ∈ s.pairs.getLast?, p.1 = s.duration := by
    have h1 : (s.pairs.map Prod.fst).getLast? = some s.duration := by
      rw [hmap]
      rcases List.eq_nil_or_concat s.time with h | ⟨init, last, h⟩
      · exact absurd h hne
      · simp [h, FiniteSignal.duration]
    rw [List.getLast?_map, Option.map_eq_some_iff] at h1
    exact h1
  -- the end is the duration exactly if `pI` is the length
  have hbeq : b = s.duration → pI = s.time.length := fun h => by
    by_contra hne'
    exact absurd (hle _ (List.getElem_mem (by omega : pI < s.time.length)))
      (not_le.mpr (h ▸ hP2 (by omega)))
  have hblt : b < s.duration → pI < s.time.length := fun h => by
    by_contra hne'
    obtain ⟨j, hj, hjD⟩ := List.getElem_of_mem hmem
    exact absurd (hjD ▸ hP1 j (by omega)) (not_le.mpr h)
  -- only the breakpoints from `pI` on matter from `b` on
  have hvalue : pI < s.pairs.length → ∀ t, b ≤ t →
      FiniteSignal.valueAt s.pairs t = FiniteSignal.valueAt (s.pairs.drop pI) t := fun hk t ht => by
    have hd : s.pairs.drop pI ≠ [] := by simp; omega
    conv_lhs => rw [← List.take_append_drop pI s.pairs]
    refine aux_valueAt_append_ge _ _ t hd fun p hp' => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
    simp only [List.length_take] at hi
    rw [List.getElem_take, hget i (by omega)]
    exact (hP1 i (by omega)).trans ht
  -- the value of the first breakpoint from `pI` on
  have hhead : ∀ hk : pI < s.pairs.length, (s.pairs.drop pI).head? =
      some (s.time[pI]'(by omega), s.value[pI]'(by omega)) := fun hk => by
    rw [hdrop pI hk]; rfl
  have hlastd : ∀ hk : pI < s.pairs.length, ∃ p ∈ (s.pairs.drop pI).getLast?,
      p.1 = s.duration := fun hk => by
    rw [List.getLast?_drop, if_neg (by omega)]; exact hlast
  by_cases hUU : U
  · rw [if_pos hUU]
    by_cases hbd : b = s.duration
    · -- the signal ends at `b`
      have hn : s.pairs.drop pI = [] := List.drop_eq_nil_of_le (by have := hbeq hbd; omega)
      rw [hn]
      refine ⟨by simp, fun p hp' => ?_, by simp, fun p hp' => ?_, by simp, ?_, fun t ht1 ht2 => ?_⟩
      · simp at hp'; subst hp'; exact ⟨le_rfl, rfl⟩
      -- rewrite and simplify
      · simp at hp'; subst hp'; exact ⟨hb0, le_rfl⟩
      · exact ⟨(b, value), by simp, hbd⟩
      · exact ⟨fun _ => by simp [FiniteSignal.valueAt], fun h => absurd hbd h.ne⟩
    · -- a boundary at `b`, then the breakpoints from `pI` on
      have hbl : b < s.duration := lt_of_le_of_ne hbD hbd
      have hk : pI < s.pairs.length := by have := hblt hbl; omega
      have hvne : s.value[pI]'(by omega) ≠ value := fun hv' => by
        rcases hU.mp hUU with h | h
        · exact hbd h
        · exact h (by rw [List.getElem?_eq_getElem (by omega), hv'])
      have hQ : s.pairs.drop pI ≠ [] := by simp; omega
      refine ⟨by simp, fun p hp' => ?_, ?_, fun p hp' => ?_, ?_, ?_, fun t ht1 ht2 => ?_⟩
      · simp at hp'; subst hp'; exact ⟨le_rfl, rfl⟩
      · rw [List.map_append, List.pairwise_append]
        -- prove the parts of the goal
        refine ⟨by simp, hsortd, fun x hx y hy => ?_⟩
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
        rw [List.map_singleton, List.mem_singleton] at hx
        rw [hx]; exact hbig q hq
      · rcases List.mem_append.mp hp' with h' | h'
        · rw [List.mem_singleton] at h'; rw [h']; exact ⟨hb0, le_rfl⟩
        · exact ⟨hnnd p h', (hbig p h').le⟩
      · rw [List.map_append, List.map_singleton, List.isChain_append]
        refine ⟨List.isChain_singleton _, hchd, fun x hx y hy => ?_⟩
        rw [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
        rw [List.head?_map, hhead hk, Option.map_some, Option.mem_def, Option.some.injEq] at hy
        rw [← hx, ← hy]
        exact hvne.symm
      · rw [List.getLast?_append_of_ne_nil _ hQ]
        -- conclude
        exact hlastd hk
      · refine ⟨fun h => absurd h hbd, fun _ => ?_⟩
        rw [List.singleton_append, FiniteSignal.valueAt_cons_of_ge _ _ t
          (not_lt.mpr (by simpa using ht1)) hQ, hvalue hk t ht1]
  · -- no boundary at `b`: the value there already is `value`
    rw [if_neg hUU]
    have hU' := not_or.mp (mt hU.mpr hUU)
    have hbd : b ≠ s.duration := hU'.1
    have hvq : s.value[pI]? = some value := not_not.mp hU'.2
    have hk : pI < s.pairs.length := by
      have := (List.getElem?_eq_some_iff.mp hvq).1; omega
    have hQ : s.pairs.drop pI ≠ [] := by simp; omega
    have hvv : s.value[pI]'(by omega) = value := by
      rwa [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hvq
    -- rewrite and simplify
    simp only [List.nil_append]
    refine ⟨hQ, fun p hp' => ?_, hsortd, fun p hp' => ⟨hnnd p hp', (hbig p hp').le⟩, hchd,
      hlastd hk, fun t ht1 ht2 => ⟨fun h => absurd h hbd, fun _ => hvalue hk t ht1 |>.symm⟩⟩
    rw [hhead hk, Option.mem_def, Option.some.injEq] at hp'
    rw [← hp']
    exact ⟨(hP2 (by omega)).le, hvv⟩

/-- Putting the two parts together: the result of `set`. -/
theorem aux_set_assemble {V : Type} [DecidableEq V] (s : FiniteSignal ℝ V) (hs : s.IsValid)
    (a b : ℝ) (hab : a < b) (value : V) (pI A : ℕ) (nT : List ℝ) (nV : List V)
    (hnl : nT.length = nV.length)
    (U : Prop) [Decidable U]
    (lsort : ((s.pairs.take A ++ nT.zip nV).map Prod.fst).Pairwise (· < ·))
    (ltimes : ∀ p ∈ s.pairs.take A ++ nT.zip nV, 0 ≤ p.1 ∧ p.1 ≤ a) -- the left part
    (lchain : ((s.pairs.take A ++ nT.zip nV).map Prod.snd).IsChain (· ≠ ·))
    (llast : ∀ p ∈ (s.pairs.take A ++ nT.zip nV).getLast?, p.2 ≠ value)
    (lpoint : ∀ t : ℝ, 0 ≤ t → t < a → ∀ W : List (ℝ × V), W ≠ [] →
      (∀ p ∈ W.head?, a < p.1 ∧ p.2 = value) →
      FiniteSignal.valueAt (s.pairs.take A ++ nT.zip nV ++ W) t = FiniteSignal.valueAt s.pairs t)
    (rne : ((if U then [(b, value)] else []) ++ s.pairs.drop pI) ≠ [])
    (rhead : ∀ p ∈ ((if U then [(b, value)] else []) ++ s.pairs.drop pI).head?,
      b ≤ p.1 ∧ p.2 = value)
    (rsort : (((if U then [(b, value)] else []) ++ s.pairs.drop pI).map Prod.fst).Pairwise (· < ·))
    (rtimes : ∀ p ∈ (if U then [(b, value)] else []) ++ s.pairs.drop pI, 0 ≤ p.1 ∧ b ≤ p.1)
    -- the right part
    (rchain : (((if U then [(b, value)] else []) ++ s.pairs.drop pI).map Prod.snd).IsChain (· ≠ ·))
    (rlast : ∃ p ∈ ((if U then [(b, value)] else []) ++ s.pairs.drop pI).getLast?,
      p.1 = s.duration)
    (rpoint : ∀ t : ℝ, b ≤ t → t ≤ s.duration →
      (b = s.duration → FiniteSignal.valueAt ((if U then [(b, value)] else []) ++
        s.pairs.drop pI) t = some value) ∧
      (b < s.duration → FiniteSignal.valueAt ((if U then [(b, value)] else []) ++
        s.pairs.drop pI) t = FiniteSignal.valueAt s.pairs t)) : -- --- STMT ---
    ∃ r, FiniteSignal.mk? (s.time.take A ++ (if U then nT ++ [b] else nT) ++ s.time.drop pI)
        (s.value.take A ++ (if U then nV ++ [value] else nV) ++ s.value.drop pI) = some r ∧
      r.IsValid ∧ r.duration = s.duration ∧ ∀ t : ℝ, 0 ≤ t → t ≤ s.duration →
        r.at? t = if a ≤ t ∧ (t < b ∨ b = s.duration) then some value
          else s.at? t := by -- --- PROOF ---
  -- unpack the facts from the previous steps
  obtain ⟨hmem, hle⟩ := FiniteSignal.time_le_duration s hs
  obtain ⟨hne, hl, hp, hch, hnn⟩ := hs
  -- the part before `a` and the part from `b` on, as lists of breakpoints
  obtain ⟨E, hE⟩ : ∃ E, E = s.pairs.take A ++ nT.zip nV := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = (if U then [(b, value)] else []) ++ s.pairs.drop pI := ⟨_, rfl⟩
  rw [← hE] at lsort ltimes lchain llast lpoint
  rw [← hW] at rne rhead rsort rtimes rchain rlast rpoint
  -- the arrays of the result are the splice
  have hn2 : (if U then nT ++ [b] else nT).length = (if U then nV ++ [value] else nV).length := by
    split_ifs <;> simp [hnl]
  obtain ⟨Rt, hRt⟩ : ∃ Rt, Rt = s.time.take A ++ (if U then nT ++ [b] else nT) ++ s.time.drop pI :=
    ⟨_, rfl⟩
  obtain ⟨Rv, hRv⟩ : ∃ Rv, Rv = s.value.take A ++ (if U then nV ++ [value] else nV) ++
      s.value.drop pI := ⟨_, rfl⟩
  rw [← hRt, ← hRv]
  have hz : Rt.zip Rv = E ++ W := by
    rw [hRt, hRv, aux_zip_splice s.time s.value A pI _ _ hl hn2, hE, hW]
    by_cases hU : U
    · simp only [hU, if_true, List.zip_append hnl, List.zip_cons_cons, List.zip_nil_right]
      simp [FiniteSignal.pairs, List.append_assoc]
    · simp only [hU, if_false]
      simp [FiniteSignal.pairs]
  -- the fact `hlen2`
  have hlen2 : Rt.length = Rv.length := by
    rw [hRt, hRv]; simp [List.length_take, List.length_drop, hl, hn2]
  have hfst : Rt = (E ++ W).map Prod.fst := by
    rw [← hz, List.map_fst_zip hlen2.le]
  have hsnd : Rv = (E ++ W).map Prod.snd := by
    rw [← hz, List.map_snd_zip hlen2.ge]
  -- the result is valid
  have hv : (⟨Rt, Rv⟩ : FiniteSignal ℝ V).IsValid := by
    rw [hfst, hsnd]
    refine ⟨by simp [rne], by simp, ?_, ?_, fun t ht => ?_⟩
    · -- ordered: the part before `a` and the part from `b` on
      rw [List.map_append, List.pairwise_append]
      refine ⟨lsort, rsort, fun x hx y hy => ?_⟩
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      exact lt_of_le_of_lt (ltimes p hp').2 (hab.trans_le (rtimes q hq).2)
    · -- alternating: the last value before differs from `value`, the first after is `value`
      show ((E ++ W).map Prod.snd).IsChain (· ≠ ·)
      rw [List.map_append, List.isChain_append]
      refine ⟨lchain, rchain, fun x hx y hy => ?_⟩
      rw [List.getLast?_map, Option.mem_def, Option.map_eq_some_iff] at hx
      -- rewrite and simplify
      rw [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hy
      obtain ⟨p, hp', rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := hy
      rw [(rhead q hq).2]
      exact llast p hp'
    · -- nonnegative
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp ht
      rcases List.mem_append.mp hp' with h' | h'
      · exact (ltimes p h').1
      · exact (rtimes p h').1
  refine ⟨⟨Rt, Rv⟩, (FiniteSignal.mk?_eq_some_iff _ _ _).mpr ⟨rfl, rfl, hv⟩, hv, ?_,
    fun t ht0 ht1 => ?_⟩
  · -- the duration is the end of the part from `b` on
    obtain ⟨q, hq, hqD⟩ := rlast
    show Rt.getLastD 0 = s.duration
    -- rewrite and simplify
    rw [List.getLastD_eq_getLast?, hfst, List.getLast?_map, List.getLast?_append]
    rw [Option.mem_def] at hq
    rw [hq]; simp [hqD]
  · -- the value at `t`
    have hdur : (⟨Rt, Rv⟩ : FiniteSignal ℝ V).duration = s.duration := by
      obtain ⟨q, hq, hqD⟩ := rlast
      show Rt.getLastD 0 = s.duration
      rw [List.getLastD_eq_getLast?, hfst, List.getLast?_map, List.getLast?_append]
      rw [Option.mem_def] at hq
      rw [hq]; simp [hqD]
    have hc1 : 0 ≤ t ∧ t ≤ (⟨Rt, Rv⟩ : FiniteSignal ℝ V).duration := ⟨ht0, hdur ▸ ht1⟩
    have hc2 : 0 ≤ t ∧ t ≤ s.duration := ⟨ht0, ht1⟩
    rw [FiniteSignal.at?_eq_valueAt _ hv.2.1 t, if_pos hc1, FiniteSignal.at?_eq_valueAt s hl t,
      if_pos hc2]
    -- rewrite and simplify
    show FiniteSignal.valueAt (Rt.zip Rv) t = _
    rw [hz]
    by_cases hta : t < a
    · -- before `a`: the signal itself
      rw [if_neg (fun h => absurd h.1 (not_le.mpr hta))]
      exact lpoint t ht0 hta W rne fun p hp' => ⟨hab.trans_le (rhead p hp').1, (rhead p hp').2⟩
    · -- from `a` on, only the part from `b` on matters
      have hat : a ≤ t := not_lt.mp hta
      rw [aux_valueAt_append_ge E W t rne fun p hp' => (ltimes p hp').2.trans hat]
      by_cases htb : t < b
      · -- between `a` and `b` the value is `value`
        rw [if_pos ⟨hat, Or.inl htb⟩]
        obtain ⟨w, W', rfl⟩ := List.exists_cons_of_ne_nil rne
        obtain ⟨hwb, hwv⟩ := rhead w (by simp)
        -- rewrite and simplify
        rw [FiniteSignal.valueAt_cons_of_lt w W' t (htb.trans_le hwb), hwv]
      · -- from `b` on
        have htb' : b ≤ t := not_lt.mp htb
        by_cases hbD : b = s.duration
        · rw [if_pos ⟨hat, Or.inr hbD⟩]; exact (rpoint t htb' ht1).1 hbD
        · rw [if_neg (by rintro ⟨-, h | h⟩ <;> contradiction)]
          exact (rpoint t htb' ht1).2 (lt_of_le_of_ne (htb'.trans ht1) hbD)


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.set?_spec {V : Type} [DecidableEq V] (s : FiniteSignal ℝ V)
    (hs : s.IsValid) (hpos : ∀ b ∈ s.time.head?, 0 < b) (lo hi : EReal) (value : V)
    (hlt : Max.max lo 0 < Min.min hi (s.duration : EReal)) : -- --- STMT ---
    ∃ r, s.set? lo hi value = some r ∧ r.IsValid ∧ r.duration = s.duration ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ s.duration → r.at? t =
        if Max.max lo 0 ≤ (t : EReal) ∧ ((t : EReal) < Min.min hi (s.duration : EReal) ∨
            Min.min hi (s.duration : EReal) = (s.duration : EReal)) then some value
        else s.at? t := by -- --- PROOF ---
  obtain ⟨hmem, hle⟩ := FiniteSignal.time_le_duration s hs
  -- the bounds are real numbers `a < b ≤ duration`
  have hlb_ne_top : Max.max lo 0 ≠ ⊤ := ne_top_of_lt (hlt.trans_le (min_le_right _ _))
  have hlb_ne_bot : Max.max lo 0 ≠ ⊥ :=
    ne_bot_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (le_max_right _ _))
  have hub_ne_top : Min.min hi (s.duration : EReal) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (min_le_right _ _)
  have hub_ne_bot : Min.min hi (s.duration : EReal) ≠ ⊥ := ne_bot_of_gt hlt
  obtain ⟨a, ha⟩ : ∃ a : ℝ, (a : EReal) = Max.max lo 0 :=
    ⟨_, EReal.coe_toReal hlb_ne_top hlb_ne_bot⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (b : EReal) = Min.min hi (s.duration : EReal) :=
    ⟨_, EReal.coe_toReal hub_ne_top hub_ne_bot⟩
  rw [← ha, ← hb] at hlt ⊢
  have ha0 : 0 ≤ a := by
    have : (0 : EReal) ≤ a := ha ▸ le_max_right _ _
    exact_mod_cast this
  -- the fact `hab`
  have hab : a < b := EReal.coe_lt_coe_iff.mp hlt
  have hbD : b ≤ s.duration := by
    have : (b : EReal) ≤ s.duration := hb ▸ min_le_right _ _
    exact_mod_cast this
  unfold FiniteSignal.set?
  dsimp only
  rw [← ha, ← hb, if_neg (not_not.mpr hlt), EReal.toReal_coe a, EReal.toReal_coe b]
  -- the indices of the cells of `a` and `b`
  obtain ⟨t1, t2⟩ := List.takeWhile_getElem (fun x : ℝ => decide (x ≤ a)) s.time
  obtain ⟨u1, u2⟩ := List.takeWhile_getElem (fun x : ℝ => decide (x ≤ b)) s.time
  have hsIle : (s.time.takeWhile (fun x : ℝ => decide (x ≤ a))).length ≤ s.time.length :=
    (List.takeWhile_sublist _).length_le
  have hpIle : (s.time.takeWhile (fun x : ℝ => decide (x ≤ b))).length ≤ s.time.length :=
    (List.takeWhile_sublist _).length_le
  set sI := (s.time.takeWhile (fun x : ℝ => decide (x ≤ a))).length with hsI
  set pI := (s.time.takeWhile (fun x : ℝ => decide (x ≤ b))).length with hpI
  have hT1 : ∀ i (hi : i < sI), s.time[i]'(by omega) ≤ a := fun i hi => by simpa using t1 i hi
  have hP1 : ∀ i (hi : i < pI), s.time[i]'(by omega) ≤ b := fun i hi => by simpa using u1 i hi
  have hP2 : ∀ (hi : pI < s.time.length), b < s.time[pI] := fun hi => by
    simpa using u2 hi
  have hsIlt : sI < s.time.length := by
    by_contra hcon
    -- unpack the facts from the previous steps
    obtain ⟨j, hj, hjD⟩ := List.getElem_of_mem hmem
    exact absurd (hjD ▸ hT1 j (by omega)) (not_le.mpr (hab.trans_le hbD))
  have hT2 : a < s.time[sI] := by simpa using t2 hsIlt
  -- the left and the right part of the result
  obtain ⟨A, nT, nV, hlow⟩ : ∃ A nT nV, s.aux_setLower a value
      (s.time.takeWhile (fun x : ℝ => decide (x ≤ a))).length = (A, nT, nV) := ⟨_, _, _, rfl⟩
  rw [hlow]
  dsimp only
  obtain ⟨-, hnl, lsort, ltimes, lchain, llast, lpoint⟩ :=
    aux_set_left s hs hpos a ha0 value sI hsIlt hT1 hT2 A nT nV hlow
  obtain ⟨rne, rhead, rsort, rtimes, rchain, rlast, rpoint⟩ := aux_set_right s hs b
    (ha0.trans hab.le) value hbD pI hpIle hP1 hP2
    (b = s.duration ∨ s.value[pI]? ≠ some value) Iff.rfl
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := aux_set_assemble s hs a b hab value pI A nT nV hnl
    (b = s.duration ∨ s.value[pI]? ≠ some value) lsort ltimes lchain llast lpoint rne rhead rsort
    rtimes rchain rlast rpoint
  refine ⟨r, hr1, hr2, hr3, fun t ht0 ht1 => ?_⟩
  rw [hr4 t ht0 ht1]
  -- rewrite and simplify
  simp only [EReal.coe_le_coe_iff, EReal.coe_lt_coe_iff, EReal.coe_eq_coe_iff]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
