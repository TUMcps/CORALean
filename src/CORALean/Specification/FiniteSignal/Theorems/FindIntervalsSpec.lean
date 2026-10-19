module

public import CORALean.Specification.FiniteSignal.Operations.CellsFrom
public import CORALean.Specification.FiniteSignal.Theorems.PairsOfValid
public import Mathlib.Order.Basic
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.FindIntervals

@[expose] public section

/-!
# What `findIntervals` computes

The intervals found are the maximal runs of cells satisfying the condition, closed at both ends as
the cells are: ordered, each with `start ≤ stop`, separated by a gap, and covering exactly the
times of those cells.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop on breakpoints `(b,v) :: rest` after the time `a`, with the run (if `cond v`) started
at `st ≤ a`: the intervals are ordered and separated, and cover the cells satisfying `cond`
together with the part `[st,a]` of the run already begun. -/
theorem aux_findIntervals_loop {T V : Type} [LinearOrder T] (cond : V → Bool) : -- --- CONCL ---
    ∀ (rest : List (T × V)) (b : T) (v : V) (a st : T),
      (((b, v) :: rest).map Prod.fst).Pairwise (· < ·) → a ≤ b → (cond v = true → st ≤ a) →
      (∀ I ∈ FiniteSignal.aux_findIntervalsLoop cond st ((b, v) :: rest), I.1 ≤ I.2) ∧
      (FiniteSignal.aux_findIntervalsLoop cond st ((b, v) :: rest)).Pairwise (fun I J => I.2 < J.1)
        ∧
      (∀ I ∈ FiniteSignal.aux_findIntervalsLoop cond st ((b, v) :: rest),
        (cond v = true ∧ st ≤ I.1) ∨ b ≤ I.1) ∧
      ∀ x, (∃ I ∈ FiniteSignal.aux_findIntervalsLoop cond st ((b, v) :: rest), I.1 ≤ x ∧ x ≤ I.2) ↔
        ((cond v = true ∧ st ≤ x ∧ x ≤ a) ∨ ∃ c ∈ FiniteSignal.cellsFrom a ((b, v) :: rest),
          cond c.2 = true ∧ c.1.1 ≤ x ∧ x ≤ c.1.2)
  | [], b, v, a, st, _, hab, hst => by
    by_cases hv : cond v = true
    · have hsa := hst hv
      simp only [FiniteSignal.aux_findIntervalsLoop, FiniteSignal.cellsFrom, hv, if_true]
      -- prove the parts of the goal
      refine ⟨by simpa using hsa.trans hab, by simp, by simp, fun x => ?_⟩
      simp only [List.mem_singleton, exists_eq_left, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hxa : x ≤ a
        · exact Or.inl ⟨h1, hxa⟩
        · exact Or.inr ⟨hv, (not_le.mp hxa).le, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨-, h1, h2⟩)
        · exact ⟨h1, h2.trans hab⟩
        · exact ⟨hsa.trans h1, h2⟩
    · simp [FiniteSignal.aux_findIntervalsLoop, FiniteSignal.cellsFrom, hv]
  | (b', v') :: rest', b, v, a, st, hs, hab, hst => by
    rw [List.map_cons, List.pairwise_cons] at hs
    have hbb' : b < b' := hs.1 b' (by simp)
    -- the fact `hs'`
    have hs' : (((b', v') :: rest').map Prod.fst).Pairwise (· < ·) := by
      rw [List.map_cons]; exact hs.2
    have hcells : FiniteSignal.cellsFrom a ((b, v) :: (b', v') :: rest') =
        ((a, b), v) :: FiniteSignal.cellsFrom b ((b', v') :: rest') := rfl
    have hcells' : FiniteSignal.cellsFrom b ((b', v') :: rest') =
        ((b, b'), v') :: FiniteSignal.cellsFrom b' rest' := rfl
    rw [hcells]
    by_cases hv : cond v = true <;> by_cases hv' : cond v' = true
    · -- both values satisfy the condition
      have hout : FiniteSignal.aux_findIntervalsLoop cond st ((b, v) :: (b', v') :: rest') =
          FiniteSignal.aux_findIntervalsLoop cond st ((b', v') :: rest') := by
        simp [FiniteSignal.aux_findIntervalsLoop, hv, hv']
      have hsa := hst hv
      obtain ⟨i1, i2, i3, i4⟩ := aux_findIntervals_loop cond rest' b' v' b st hs' hbb'.le
        (fun _ => hsa.trans hab)
      -- rewrite and simplify
      rw [hout]
      refine ⟨i1, i2, fun I hI => ?_, fun x => ?_⟩
      · rcases i3 I hI with h | h
        · exact Or.inl ⟨hv, h.2⟩
        · exact Or.inr (hbb'.le.trans h)
      · rw [i4 x]
        constructor
        · rintro (⟨-, h1, h2⟩ | ⟨c, hc, h⟩)
          · by_cases hxa : x ≤ a
            · exact Or.inl ⟨hv, h1, hxa⟩
            · exact Or.inr ⟨((a, b), v), by simp, hv, (not_le.mp hxa).le, h2⟩
          · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, h⟩
        · rintro (⟨-, h1, h2⟩ | ⟨c, hc, h⟩)
          · exact Or.inl ⟨hv', h1, h2.trans hab⟩
          -- split into the cases
          · rcases List.mem_cons.mp hc with rfl | hc
            · exact Or.inl ⟨hv', hsa.trans h.2.1, h.2.2⟩
            · exact Or.inr ⟨c, hc, h⟩
    · -- a falling edge
      have hout : FiniteSignal.aux_findIntervalsLoop cond st ((b, v) :: (b', v') :: rest') =
          [(st, b)] ++ FiniteSignal.aux_findIntervalsLoop cond st ((b', v') :: rest') := by
        simp [FiniteSignal.aux_findIntervalsLoop, hv, hv']
      have hsa := hst hv
      obtain ⟨i1, i2, i3, i4⟩ := aux_findIntervals_loop cond rest' b' v' b st hs' hbb'.le
        (by simp [hv'])
      have hge : ∀ J ∈ FiniteSignal.aux_findIntervalsLoop cond st ((b', v') :: rest'), b' ≤ J.1 :=
        by
        intro J hJ
        rcases i3 J hJ with h | h
        · simp [hv'] at h
        -- conclude
        · exact h
      rw [hout]
      refine ⟨fun I hI => ?_, ?_, fun I hI => ?_, fun x => ?_⟩
      · rcases List.mem_append.mp hI with h | h
        · rw [List.mem_singleton.mp h]; exact hsa.trans hab
        · exact i1 I h
      · rw [List.pairwise_append]
        exact ⟨by simp, i2, fun I hI J hJ => by
          rw [List.mem_singleton.mp hI]; exact hbb'.trans_le (hge J hJ)⟩
      · rcases List.mem_append.mp hI with h | h
        · rw [List.mem_singleton.mp h]; exact Or.inl ⟨hv, le_rfl⟩
        · exact Or.inr (hbb'.le.trans (hge I h))
      · simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨I, rfl | hI, h1, h2⟩
          -- split on whether the condition holds
          · by_cases hxa : x ≤ a
            · exact Or.inl ⟨hv, h1, hxa⟩
            · exact Or.inr ⟨((a, b), v), by simp, hv, (not_le.mp hxa).le, h2⟩
          · obtain h | ⟨c, hc, h⟩ := (i4 x).mp ⟨I, hI, h1, h2⟩
            · simp [hv'] at h
            · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, h⟩
        · rintro (⟨-, h1, h2⟩ | ⟨c, hc, h⟩)
          · exact ⟨(st, b), Or.inl rfl, h1, h2.trans hab⟩
          · rcases List.mem_cons.mp hc with rfl | hc
            · exact ⟨(st, b), Or.inl rfl, hsa.trans h.2.1, h.2.2⟩
            · obtain ⟨I, hI, h'⟩ := (i4 x).mpr (Or.inr ⟨c, hc, h⟩)
              exact ⟨I, Or.inr hI, h'⟩
    · -- a rising edge
      have hout : FiniteSignal.aux_findIntervalsLoop cond st ((b, v) :: (b', v') :: rest') =
          FiniteSignal.aux_findIntervalsLoop cond b ((b', v') :: rest') := by
        -- rewrite and simplify
        simp [FiniteSignal.aux_findIntervalsLoop, hv, hv']
      obtain ⟨i1, i2, i3, i4⟩ := aux_findIntervals_loop cond rest' b' v' b b hs' hbb'.le
        (fun _ => le_rfl)
      rw [hout]
      refine ⟨i1, i2, fun I hI => ?_, fun x => ?_⟩
      · rcases i3 I hI with ⟨-, h⟩ | h
        · exact Or.inr h
        · exact Or.inr (hbb'.le.trans h)
      · rw [i4 x]
        constructor
        · rintro (⟨-, h1, h2⟩ | ⟨c, hc, h⟩)
          · refine Or.inr ⟨((b, b'), v'), ?_, hv', h1, h2.trans hbb'.le⟩
            rw [hcells']; simp
          · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, h⟩
        · rintro (⟨h, -⟩ | ⟨c, hc, h⟩)
          -- rewrite and simplify
          · simp [hv] at h
          · rcases List.mem_cons.mp hc with rfl | hc
            · simp [hv] at h
            · exact Or.inr ⟨c, hc, h⟩
    · -- neither value satisfies the condition
      have hout : FiniteSignal.aux_findIntervalsLoop cond st ((b, v) :: (b', v') :: rest') =
          FiniteSignal.aux_findIntervalsLoop cond st ((b', v') :: rest') := by
        simp [FiniteSignal.aux_findIntervalsLoop, hv, hv']
      obtain ⟨i1, i2, i3, i4⟩ := aux_findIntervals_loop cond rest' b' v' b st hs' hbb'.le
        (by simp [hv'])
      rw [hout]
      refine ⟨i1, i2, fun I hI => ?_, fun x => ?_⟩
      · rcases i3 I hI with h | h
        · simp [hv'] at h
        -- conclude
        · exact Or.inr (hbb'.le.trans h)
      · rw [i4 x]; simp [hv, hv']


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.findIntervals_spec {T V : Type} [LinearOrder T] [Zero T] (s : FiniteSignal T V)
    (hs : s.IsValid) (cond : V → Bool) : -- --- CONCL ---
    (∀ I ∈ s.findIntervals cond, I.1 ≤ I.2) ∧
      (s.findIntervals cond).Pairwise (fun I J => I.2 < J.1) ∧
      ∀ x, (∃ I ∈ s.findIntervals cond, I.1 ≤ x ∧ x ≤ I.2) ↔
        ∃ c ∈ s.cells, cond c.2 = true ∧ c.1.1 ≤ x ∧ x ≤ c.1.2 := by -- --- PROOF ---
  obtain ⟨b, v, rest, hq, hmap, -, hb0⟩ := FiniteSignal.pairs_of_valid s hs
  have hsorted : (((b, v) :: rest).map Prod.fst).Pairwise (· < ·) := hq ▸ hmap ▸ hs.2.2.1
  obtain ⟨i1, i2, -, i4⟩ := aux_findIntervals_loop cond rest b v 0 0 hsorted hb0
    (fun _ => le_rfl)
  have hout : s.findIntervals cond = FiniteSignal.aux_findIntervalsLoop cond 0 ((b, v) :: rest) :=
    by
    unfold FiniteSignal.findIntervals; rw [hq]
  have hcells : s.cells = FiniteSignal.cellsFrom 0 ((b, v) :: rest) := by
    unfold FiniteSignal.cells; rw [← hq]; rfl
  -- rewrite and simplify
  rw [hout, hcells]
  refine ⟨i1, i2, fun x => ?_⟩
  rw [i4 x]
  constructor
  · rintro (⟨hv, h1, h2⟩ | h)
    · -- the part `[0,0]` of the first run is inside the first cell
      have hx : x = 0 := le_antisymm h2 h1
      subst hx
      exact ⟨((0, b), v), by simp [FiniteSignal.cellsFrom], hv, le_rfl, hb0⟩
    · exact h
  · exact Or.inr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
