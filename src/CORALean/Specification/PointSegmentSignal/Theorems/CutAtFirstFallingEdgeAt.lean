module

public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellMono
public import CORALean.Specification.PointSegmentSignal.Theorems.CutAtFirstFallingEdgeSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.ExistsCellEq
public import CORALean.Specification.PointSegmentSignal.Theorems.AtEqCell

@[expose] public section

/-!
# Cutting a signal where it first falls, in time

In dense time without a last moment, `cutAtFirstFallingEdge(obj)` is `true` at `t ≥ 0` iff the
signal is `true` at `t` and no time up to `t` has the signal `true` and a later one up to `t`
`false`.

## Inputs
* `T` – time type
* `s` – signal
* `t` – time

## Hypotheses
* `hs` – the signal is valid
* `ht` – the time is nonnegative

## Conclusion
* the cut signal is true iff the signal is true and has not fallen
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An earlier value is read at an earlier time. -/
theorem PointSegmentSignal.aux_exists_cell_le {T : Type} [LinearOrder T] [Zero T] [DenselyOrdered T]
    [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (t : T) (ht : 0 ≤ t) (c : ℕ)
    (hc : c ≤ s.cell t) : -- --- CONCL ---
    ∃ t', 0 ≤ t' ∧ t' ≤ t ∧ s.cell t' = c := by -- --- PROOF ---
  rcases hc.eq_or_lt with h | h
  · exact ⟨t, ht, le_rfl, h.symm⟩
  · -- a time reading the earlier value is not after `t`
    obtain ⟨t', ht', hct⟩ := s.exists_cell_eq hs c (lt_trans h (s.cell_lt hs t ht))
    refine ⟨t', ht', ?_, hct⟩
    by_contra hlt
    have := s.cell_mono hs t t' ht (not_le.1 hlt).le
    omega


-- =======================================  MAIN THEOREM  ======================================= --

/-- The cut signal is `true` where the signal is `true` and has not fallen by then. -/
theorem PointSegmentSignal.cutAtFirstFallingEdge_at {T : Type} [LinearOrder T] [Zero T]
    [DenselyOrdered T] [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (t : T)
    (ht : 0 ≤ t) : -- --- CONCL ---
    s.cutAtFirstFallingEdge.at t = true ↔ s.at t = true ∧
      ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t → s.at t₁ = true → s.at t₂ = true := by -- --- PROOF ---
  rw [(s.cutAtFirstFallingEdge_spec hs).2 t ht]
  refine and_congr_right fun _ => ⟨fun h t₁ t₂ h1 h12 h2 hv => ?_, fun h c₁ c₂ h12 h2 hv => ?_⟩
  · -- times reading the values: the indices are in order
    have hc1 := s.cell_mono hs t₁ t₂ h1 h12
    have hc2 := s.cell_mono hs t₂ t (h1.trans h12) h2
    rw [PointSegmentSignal.at_eq_cell] at hv ⊢
    exact h _ _ hc1 hc2 hv
  · -- times reading the indices, each not after the next
    obtain ⟨t₂, h20, h2t, hc2⟩ := s.aux_exists_cell_le hs t ht c₂ h2
    obtain ⟨t₁, h10, h12', hc1⟩ := s.aux_exists_cell_le hs t₂ h20 c₁ (hc2 ▸ h12)
    have := h t₁ t₂ h10 h12' h2t (by rw [PointSegmentSignal.at_eq_cell, hc1]; exact hv)
    rwa [PointSegmentSignal.at_eq_cell, hc2] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
