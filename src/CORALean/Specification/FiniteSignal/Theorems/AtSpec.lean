module

public import CORALean.Specification.FiniteSignal.Theorems.AtEqValueAt
public import CORALean.Specification.FiniteSignal.Theorems.CellsFromBounds
public import CORALean.Specification.FiniteSignal.Theorems.TimeLeDuration

@[expose] public section

/-!
# What `at` reads

For a valid signal, `at(sig,time)` returns the value of the cell containing the time: the cells
`[lo,hi)` between consecutive breakpoints, the last one closed at its right end. It throws exactly
outside `[0, duration]`.

## Inputs
* `T` – time type
* `V` – value type
* `s` – signal
* `t` – time
* `v` – value to look up

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* `at` returns the value iff a cell containing the time holds it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The cell semantics of `valueAt` on breakpoints after `a`, with last time `d`. -/
theorem aux_valueAt_cellsFrom {T V : Type} [LinearOrder T] (d t : T) : -- --- CONCL ---
    ∀ (a : T) (L : List (T × V)) (v : V), L ≠ [] → (L.map Prod.fst).Pairwise (· < ·) →
      (∀ x ∈ L, a ≤ x.1 ∧ x.1 ≤ d) → (∃ x ∈ L, x.1 = d) → a ≤ t → t ≤ d →
      (FiniteSignal.valueAt L t = some v ↔ ∃ c ∈ FiniteSignal.cellsFrom a L, c.2 = v ∧
        c.1.1 ≤ t ∧ (t < c.1.2 ∨ (t = c.1.2 ∧ c.1.2 = d)))
  | _, [], _, h, _, _, _, _, _ => absurd rfl h
  | a, [(b, w)], v, _, _, hb, _, hat, htd => by
    have hbd : b = d := by -- --- PROOF ---
      obtain ⟨x, hx, hxd⟩ := ‹∃ x ∈ [(b, w)], x.1 = d›
      rw [List.mem_singleton.mp hx] at hxd; exact hxd
    simp only [FiniteSignal.valueAt, FiniteSignal.cellsFrom, Option.some.injEq,
      List.mem_singleton, exists_eq_left]
    refine ⟨fun h => ⟨h, hat, ?_⟩, fun h => h.1⟩
    rcases lt_or_eq_of_le (hbd ▸ htd : t ≤ b) with h | h
    -- conclude
    · exact Or.inl h
    · exact Or.inr ⟨h, hbd⟩
  | a, (b, w) :: x :: rest, v, _, hs, hb, hd, hat, htd => by
    rw [List.map_cons, List.pairwise_cons] at hs
    have hbx : b < x.1 := hs.1 x.1 (by simp)
    have hrest : ∀ y ∈ x :: rest, b ≤ y.1 ∧ y.1 ≤ d := fun y hy =>
      ⟨(hs.1 y.1 (List.mem_map_of_mem hy)).le, (hb y (by simp [hy])).2⟩
    have hv : FiniteSignal.valueAt ((b, w) :: x :: rest) t =
        if t < b then some w else FiniteSignal.valueAt (x :: rest) t := rfl
    have hcs : FiniteSignal.cellsFrom a ((b, w) :: x :: rest) =
        ((a, b), w) :: FiniteSignal.cellsFrom b (x :: rest) := rfl
    rw [hv, hcs]
    simp only [List.mem_cons]
    by_cases hlt : t < b
    -- rewrite and simplify
    · simp only [hlt, if_true, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨_, Or.inl rfl, rfl, hat, Or.inl hlt⟩
      · rintro ⟨c, rfl | hc, hcv, hlo, -⟩
        · exact hcv
        · exact absurd hlo (not_le.mpr (hlt.trans_le (FiniteSignal.cellsFrom_bounds b (x :: rest)
            (by simpa using hs.2) (fun y hy => (hrest y hy).1) c hc).1))
    · have hbt : b ≤ t := not_lt.mp hlt
      have hbd : b ≠ d := by
        have := (hb x (by simp)).2; intro h; exact absurd (h ▸ hbx) (not_lt.mpr this)
      rw [if_neg hlt]
      have ih := aux_valueAt_cellsFrom d t b (x :: rest) v (by simp) (by simpa using hs.2) hrest
        (by obtain ⟨y, hy, hyd⟩ := hd; rcases List.mem_cons.mp hy with rfl | hy
            · exact absurd hyd hbd
            -- conclude
            · exact ⟨y, hy, hyd⟩) hbt htd
      rw [ih]
      constructor
      · rintro ⟨c, hc, h⟩; exact ⟨c, Or.inr hc, h⟩
      · rintro ⟨c, rfl | hc, h⟩
        · exfalso
          rcases h.2.2 with h' | ⟨h', h''⟩
          · exact hlt h'
          · exact hbd h''
        · exact ⟨c, hc, h⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.at?_spec {T V : Type} [LinearOrder T] [Zero T] (s : FiniteSignal T V)
    (hs : s.IsValid) (t : T) (v : V) : -- --- CONCL ---
    s.at? t = some v ↔ 0 ≤ t ∧ t ≤ s.duration ∧ ∃ c ∈ s.cells, c.2 = v ∧ c.1.1 ≤ t ∧
      (t < c.1.2 ∨ (t = c.1.2 ∧ c.1.2 = s.duration)) := by -- --- PROOF ---
  obtain ⟨hmem, hle⟩ := FiniteSignal.time_le_duration s hs
  obtain ⟨hne, hl, hp, -, hnn⟩ := hs
  rw [FiniteSignal.at?_eq_valueAt s hl]
  by_cases hr : 0 ≤ t ∧ t ≤ s.duration
  · rw [if_pos hr]
    simp only [hr.1, hr.2, true_and]
    refine aux_valueAt_cellsFrom s.duration t 0 s.pairs v ?_ ?_ ?_ ?_ hr.1 hr.2
    · intro h
      exact hne (List.eq_nil_of_length_eq_zero (by
        have := congrArg List.length h; simpa [FiniteSignal.pairs, hl] using this))
    · simpa [FiniteSignal.pairs, List.map_fst_zip, hl] using hp
    -- introduce the variables
    · intro x hx
      have hx1 := (List.of_mem_zip hx).1
      exact ⟨hnn _ hx1, hle _ hx1⟩
    · obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hmem
      refine ⟨(s.time[i], s.value[i]'(hl ▸ hi)), ?_, hix⟩
      have hi' : i < s.pairs.length := by
        rw [FiniteSignal.pairs, List.length_zip, ← hl, min_self]; exact hi
      exact List.mem_iff_getElem.mpr ⟨i, hi', by simp [FiniteSignal.pairs]⟩
  · rw [if_neg hr]
    constructor
    · intro h; cases h
    · rintro ⟨h1, h2, -⟩; exact absurd ⟨h1, h2⟩ hr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
