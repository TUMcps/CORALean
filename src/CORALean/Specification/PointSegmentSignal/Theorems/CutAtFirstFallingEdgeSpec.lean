module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.CutAtFirstFallingEdge
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLt
public import CORALean.Specification.PointSegmentSignal.Theorems.CellTake
public import CORALean.Specification.PointSegmentSignal.Theorems.FirstFallingEdge
public import Mathlib.Algebra.Order.Group.Nat
public import CORALean.Specification.PointSegmentSignal.Theorems.AtEqCell

@[expose] public section

/-!
# Cutting a signal where it first falls

For a valid signal, `cutAtFirstFallingEdge(obj)` is valid and, at a time `t ≥ 0`, `true` iff the
signal is `true` at `t` and has not fallen before: any stored value up to the one `t` reads that is
`true` is followed by `true` values up to it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Stepwise rise up to `M` is monotone up to `M`. -/
theorem aux_mono_of_step (v : List Bool) (M : ℕ)
    (hstep : ∀ c, c + 1 ≤ M → v.getD c false = true → v.getD (c + 1) false = true) :
    ∀ c₁ c₂, c₁ ≤ c₂ → c₂ ≤ M → v.getD c₁ false = true → v.getD c₂ false = true := by
  intro c₁ c₂ h12
  induction c₂, h12 using Nat.le_induction with
  | base => intro _ h; exact h
  | succ c₂ hc ih => exact fun hM h => hstep c₂ hM (ih (by omega) h)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The cut signal is `true` where the signal is `true` and has not yet fallen. -/
theorem PointSegmentSignal.cutAtFirstFallingEdge_spec {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) : -- --- CONCL ---
    s.cutAtFirstFallingEdge.IsValid ∧
      ∀ t : T, 0 ≤ t → (s.cutAtFirstFallingEdge.at t = true ↔ s.at t = true ∧
        ∀ c₁ c₂, c₁ ≤ c₂ → c₂ ≤ s.cell t → s.values.getD c₁ false = true →
          s.values.getD c₂ false = true) := by -- --- PROOF ---
  have hlen := hs.2.1
  obtain ⟨hnone, hsome⟩ := List.first_falling_edge s.values
  unfold PointSegmentSignal.cutAtFirstFallingEdge
  split
  · -- there is no falling edge: the signal stays, and never falls
    rename_i heq
    refine ⟨hs, fun t ht => ?_⟩
    have hmono := aux_mono_of_step s.values (s.values.length - 1) (fun c hc hv =>
      hnone heq (c + 1) (by omega) (by omega) (by simpa using hv))
    have hc := s.cell_lt hs t ht
    exact ⟨fun h => ⟨h, fun c₁ c₂ h12 h2 h1 => hmono c₁ c₂ h12 (by omega) h1⟩, fun h => h.1⟩
  · rename_i i heq
    obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := hsome i heq
    -- the signal does not fall before the value `i - 1`
    have hmono : ∀ c₁ c₂, c₁ ≤ c₂ → c₂ ≤ i - 1 → s.values.getD c₁ false = true →
        s.values.getD c₂ false = true :=
      aux_mono_of_step s.values (i - 1) (fun c hc hv =>
        hi5 (c + 1) (by omega) (by omega) (by simpa using hv))
    -- a cut keeping `k` points, with `false` from the value `i`
    have key : ∀ (k : ℕ) (tl : List Bool), (∀ x ∈ tl, x = false) → 1 ≤ k →
        k ≤ s.timePoints.length → (i = 2 * k - 1 ∨ i = 2 * k - 2) → tl.length = 2 * k - i →
        (PointSegmentSignal.mk (s.timePoints.take k) (s.values.take i ++ tl)).IsValid ∧
        ∀ t : T, 0 ≤ t → ((PointSegmentSignal.mk (s.timePoints.take k)
          (s.values.take i ++ tl)).at t = true ↔ s.at t = true ∧ ∀ c₁ c₂, c₁ ≤ c₂ →
            c₂ ≤ s.cell t → s.values.getD c₁ false = true → s.values.getD c₂ false = true) := by
      intro k tl htl hk1 hk2 hik hl
      -- the values of the cut signal: those of the signal before `i`, `false` from `i`
      have hvals : ∀ c, (s.values.take i ++ tl).getD c false =
          if c < i then s.values.getD c false else false := by
        intro c
        by_cases hc : c < i
        · rw [if_pos hc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hc]
        · rw [if_neg hc, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by simp; omega)]
          rcases h : tl[c - (s.values.take i).length]? with _ | x
          · simp
          · simp [htl x (List.mem_of_getElem? h)]
      have hlen' : (s.values.take i ++ tl).length = 2 * (s.timePoints.take k).length := by
        simp only [List.length_append, List.length_take]
        omega
      refine ⟨⟨?_, hlen', ?_, ?_, fun j hj1 hj2 => ?_⟩, fun t ht => ?_⟩
      · -- the time points are not empty
        have : 0 < (s.timePoints.take k).length := by simp only [List.length_take]; omega
        exact List.ne_nil_of_length_pos this
      · -- the first time point is `0`
        simp only [List.head?_take]
        rw [if_neg (by omega)]
        exact hs.2.2.1
      · exact hs.2.2.2.1.sublist (List.take_sublist _ _)
      · -- no time point has the same value as both its neighbours
        simp only [List.length_take] at hj2
        rw [hvals, hvals, hvals]
        by_cases hj : 2 * j + 1 < i
        · rw [if_pos hj, if_pos (by omega), if_pos (by omega)]
          exact hs.2.2.2.2 j hj1 (by omega)
        · -- the last time point kept: the value before it is `true`, one of those after is `false`
          have hjk : j = k - 1 := by omega
          rcases hik with hik | hik
          · -- `2 j = i - 1`: the value there is `true`, the next one `false`
            have e1 : (if 2 * j < i then s.values.getD (2 * j) false else false) = true := by
              rw [if_pos (by omega), show 2 * j = i - 1 by omega]; exact hi3
            rw [e1, if_neg hj]
            simp
          · -- `2 j = i`: the value there is `false`, the one before it `true`
            have e3 : (if 2 * j - 1 < i then s.values.getD (2 * j - 1) false else false) =
                true := by
              rw [if_pos (by omega), show 2 * j - 1 = i - 1 by omega]; exact hi3
            rw [if_neg (show ¬ 2 * j < i by omega), e3]
            simp
      · -- the value of the cut signal at `t`
        rw [PointSegmentSignal.at_eq_cell]
        simp only []
        rw [PointSegmentSignal.cell_take s hs k hk1 hk2 _ t ht, hvals]
        have hct := s.cell_lt hs t ht
        rw [PointSegmentSignal.at_eq_cell]
        -- the value read is before the cut, or the last one
        by_cases hc : s.cell t ≤ 2 * k - 1
        · rw [if_pos hc]
          constructor
          · intro h
            have hlt : s.cell t < i := by
              by_contra hn
              rw [if_neg hn] at h
              exact absurd h (by simp)
            rw [if_pos hlt] at h
            exact ⟨h, fun c₁ c₂ h12 h2 h1 => hmono c₁ c₂ h12 (by omega) h1⟩
          · rintro ⟨h1, h2⟩
            have hlt : s.cell t < i := by
              by_contra hn
              have := h2 (i - 1) i (by omega) (by omega) hi3
              rw [hi4] at this
              exact absurd this (by simp)
            rw [if_pos hlt]
            exact h1
        -- the value read is past the cut: it is `false`
        · rw [if_neg hc]
          have hge : ¬ 2 * k - 1 < i := by omega
          rw [if_neg hge]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨-, h2⟩
            have := h2 (i - 1) i (by omega) (by omega) hi3
            rw [hi4] at this
            exact absurd this (by simp)
    by_cases hodd : i % 2 ≠ 0
    · rw [if_pos hodd]
      exact key ((i + 1) / 2) [false] (by simp) (by omega) (by omega) (Or.inl (by omega))
        (by simp; omega)
    · rw [if_neg hodd]
      exact key (i / 2 + 1) [false, false] (by simp) (by omega) (by omega) (Or.inr (by omega))
        (by simp; omega)
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
