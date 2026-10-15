module

public import CORALean.Specification.FiniteSignal.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.Operations.Max
public import CORALean.Specification.FiniteSignal.Theorems.CellsIndex
public import CORALean.Specification.FiniteSignal.Theorems.TakeWhileGetElem

@[expose] public section

/-!
# What `max` computes

For a valid signal and an interval within `[0,∞)`, `max` is the largest of `0` and the values of
the cells that meet the interval: a cell `[lo_m, hi_m]`, closed at both ends, meets `[lo,hi]` if
`lo ≤ hi_m` and `lo_m ≤ hi`. So at a breakpoint inside or at the end of the interval the values on
both sides count.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The fold of `max` over the entries satisfying `P` is the largest of the start and those. -/
theorem aux_foldl_max {α V : Type} [LinearOrder V] (P : α → Prop) [DecidablePred P] (f : α → V) :
    ∀ (l : List α) (v0 : V),
      v0 ≤ l.foldl (fun v j => if P j then Max.max v (f j) else v) v0 ∧
      (∀ j ∈ l, P j → f j ≤ l.foldl (fun v j => if P j then Max.max v (f j) else v) v0) ∧
      (l.foldl (fun v j => if P j then Max.max v (f j) else v) v0 = v0 ∨
        ∃ j ∈ l, P j ∧ f j = l.foldl (fun v j => if P j then Max.max v (f j) else v) v0)
  | [], v0 => by simp
  | j :: l, v0 => by
    by_cases hp : P j
    · obtain ⟨i1, i2, i3⟩ := aux_foldl_max P f l (Max.max v0 (f j))
      simp only [List.foldl_cons, hp, if_true]
      refine ⟨le_trans (le_max_left _ _) i1, fun j' hj' hp' => ?_, ?_⟩
      · rcases List.mem_cons.mp hj' with rfl | hj'
        · exact le_trans (le_max_right _ _) i1
        -- conclude
        · exact i2 j' hj' hp'
      · rcases i3 with h | ⟨j', hj', hp', hf⟩
        · rcases max_choice v0 (f j) with h' | h'
          · exact Or.inl (h.trans h')
          · exact Or.inr ⟨j, List.mem_cons_self, hp, (h.trans h').symm⟩
        · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', hp', hf⟩
    · obtain ⟨i1, i2, i3⟩ := aux_foldl_max P f l v0
      simp only [List.foldl_cons, hp, if_false]
      refine ⟨i1, fun j' hj' hp' => ?_, ?_⟩
      · rcases List.mem_cons.mp hj' with rfl | hj'
        · exact absurd hp' hp
        · exact i2 j' hj' hp'
      · rcases i3 with h | ⟨j', hj', hp', hf⟩
        · exact Or.inl h
        -- conclude
        · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', hp', hf⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.max_spec {V : Type} [LinearOrder V] [Zero V] (s : FiniteSignal ℝ V)
    (hs : s.IsValid) (lo hi : EReal) (hlh : lo ≤ hi) (h0 : (0 : EReal) ≤ hi) :
    0 ≤ s.max lo hi ∧ (∀ c ∈ s.cells, lo ≤ (c.1.2 : EReal) → (c.1.1 : EReal) ≤ hi →
        c.2 ≤ s.max lo hi) ∧
      (s.max lo hi = 0 ∨ ∃ c ∈ s.cells, lo ≤ (c.1.2 : EReal) ∧ (c.1.1 : EReal) ≤ hi ∧
        c.2 = s.max lo hi) := by -- --- PROOF ---
  obtain ⟨hne, hl, hp, -, hnn⟩ := hs
  -- the cells by index
  have hcell : ∀ c ∈ s.cells, ∃ m, ∃ hm : m < s.time.length, c.1.2 = s.time[m] ∧
      c.2 = s.value[m]'(hl ▸ hm) ∧ (m = 0 → c.1.1 = 0) ∧
      ∀ hm0 : m ≠ 0, c.1.1 = s.time[m - 1]'(by omega) := by
    intro c hc
    obtain ⟨m, hm, rfl⟩ := (FiniteSignal.mem_cellsFrom_iff c 0 (s.time.zip s.value)).mp hc
    have hm' : m < s.time.length := by simpa [hl] using hm
    refine ⟨m, hm', by simp, by simp, fun h => by simp [h], fun h => by simp [h]⟩
  have hcell' : ∀ (m : ℕ) (hm : m < s.time.length), ∃ c ∈ s.cells, c.1.2 = s.time[m] ∧
      c.2 = s.value[m]'(hl ▸ hm) ∧ (m = 0 → c.1.1 = 0) ∧
      ∀ hm0 : m ≠ 0, c.1.1 = s.time[m - 1]'(by omega) := by
    intro m hm
    have hm2 : m < (s.time.zip s.value).length := by simpa [hl] using hm
    refine ⟨_, (FiniteSignal.mem_cellsFrom_iff _ 0 (s.time.zip s.value)).mpr ⟨m, hm2, rfl⟩,
      by simp, by simp, fun h => by simp [h], fun h => by simp [h]⟩
  -- the breakpoint where the interval begins
  obtain ⟨t1, t2⟩ := List.takeWhile_getElem (fun t : ℝ => decide ((t : EReal) < lo)) s.time
  have hk0n : (s.time.takeWhile (fun t : ℝ => decide ((t : EReal) < lo))).length ≤ s.time.length :=
    (List.takeWhile_sublist _).length_le
  set k0 := (s.time.takeWhile (fun t : ℝ => decide ((t : EReal) < lo))).length with hk0
  have hbelow : ∀ m (hm : m < k0), ((s.time[m]'(by omega) : ℝ) : EReal) < lo := fun m hm => by
    simpa using t1 m (by omega)
  have habove : ∀ hk : k0 < s.time.length, lo ≤ ((s.time[k0] : ℝ) : EReal) := fun hk => by
    have := t2 (by omega); simpa using this
  have hmono : ∀ a b (ha : a < s.time.length) (hb : b < s.time.length), a ≤ b →
      s.time[a] ≤ s.time[b] := fun a b ha hb hab => by
    rcases hab.lt_or_eq with h | rfl
    · exact (List.pairwise_iff_getElem.mp hp a b ha hb h).le
    · exact le_rfl
  -- the loop
  have hmax : s.max lo hi = (List.range' k0 (s.time.length - 1 - k0)).foldl (fun val j =>
      if (s.time.getD j 0 : EReal) ≤ hi then Max.max val (s.value.getD (j + 1) 0) else val)
      (match s.value[k0]? with | some v => Max.max 0 v | none => 0) := by
    unfold FiniteSignal.max FiniteSignal.length
    rfl
  obtain ⟨r1, r2, r3⟩ := aux_foldl_max (fun j => (s.time.getD j 0 : EReal) ≤ hi)
    (fun j => s.value.getD (j + 1) 0) (List.range' k0 (s.time.length - 1 - k0))
    (match s.value[k0]? with | some v => Max.max 0 v | none => 0)
  rw [← hmax] at r1 r2 r3
  -- the value at the breakpoint where the interval begins
  obtain ⟨V0, hV0⟩ : ∃ V0 : V, V0 = (match s.value[k0]? with
    | some v => Max.max 0 v
    | none => 0) := ⟨_, rfl⟩
  rw [← hV0] at r1 r3
  have hv0 : 0 ≤ V0 ∧ (∀ hk : k0 < s.time.length, s.value[k0]'(hl ▸ hk) ≤ V0) ∧
      (V0 = 0 ∨ ∃ hk : k0 < s.time.length, V0 = s.value[k0]'(hl ▸ hk)) := by
    by_cases hk : k0 < s.time.length
    · rw [List.getElem?_eq_getElem (hl ▸ hk)] at hV0
      subst hV0
      refine ⟨le_max_left _ _, fun _ => le_max_right _ _, ?_⟩
      rcases max_choice (0 : V) (s.value[k0]'(hl ▸ hk)) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hk, h⟩
    · rw [List.getElem?_eq_none (by omega)] at hV0
      subst hV0
      -- conclude
      exact ⟨le_rfl, fun h => absurd h hk, Or.inl rfl⟩
  have hget : ∀ j (hj : j < s.time.length), s.time.getD j 0 = s.time[j] := fun j hj => by
    simp [List.getD_eq_getElem?_getD, hj]
  have hgetv : ∀ j (hj : j < s.time.length), s.value.getD j 0 = s.value[j]'(hl ▸ hj) :=
      fun j hj => by
    simp [List.getD_eq_getElem?_getD, hl ▸ hj]
  refine ⟨hv0.1.trans r1, fun c hc hlo hhi => ?_, ?_⟩
  · -- every cell meeting the interval is below the maximum
    obtain ⟨m, hm, e1, e2, e3, e4⟩ := hcell c hc
    rw [e1] at hlo
    by_cases hmk : m < k0
    · exact absurd hlo (not_le.mpr (hbelow m hmk))
    · rcases (not_lt.mp hmk).lt_or_eq with hgt | heq
      · -- a later cell: its value is one the loop takes
        have hj : m - 1 ∈ List.range' k0 (s.time.length - 1 - k0) := by
          -- rewrite and simplify
          rw [List.mem_range'_1]; omega
        have hP : (s.time.getD (m - 1) 0 : EReal) ≤ hi := by
          rw [hget _ (by omega), ← e4 (by omega)]; exact hhi
        have := r2 (m - 1) hj hP
        rw [e2]
        rw [show m - 1 + 1 = m by omega, hgetv _ hm] at this
        exact this
      · subst heq
        rw [e2]; exact (hv0.2.1 hm).trans r1
  · rcases r3 with h | ⟨j, hj, hP, hf⟩
    · rcases hv0.2.2 with h0' | ⟨hk, h1⟩
      · exact Or.inl (h.trans h0')
      · -- the first cell of the interval
        obtain ⟨c, hc, e1, e2, e3, e4⟩ := hcell' k0 hk
        -- prove the parts of the goal
        refine Or.inr ⟨c, hc, ?_, ?_, ?_⟩
        · rw [e1]; exact habove hk
        · by_cases hk0 : k0 = 0
          · rw [e3 hk0]; simpa using h0
          · rw [e4 hk0]; exact (hbelow (k0 - 1) (by omega)).le.trans hlh
        · rw [e2, h, h1]
    · rw [List.mem_range'_1] at hj
      have hj1 : j + 1 < s.time.length := by omega
      obtain ⟨c, hc, e1, e2, e3, e4⟩ := hcell' (j + 1) hj1
      refine Or.inr ⟨c, hc, ?_, ?_, ?_⟩
      · rw [e1]
        exact (habove (by omega)).trans
          (by exact_mod_cast hmono k0 (j + 1) (by omega) hj1 (by omega))
      · rw [e4 (by omega)]
        have h' := hP
        -- rewrite and simplify
        rw [hget j (by omega)] at h'
        simpa using h'
      · rw [e2, ← hf]; exact (hgetv (j + 1) hj1).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
