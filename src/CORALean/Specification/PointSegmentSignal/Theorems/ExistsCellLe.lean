module

public import CORALean.Specification.PointSegmentSignal.Theorems.CellMono
public import CORALean.Specification.PointSegmentSignal.Theorems.ExistsCellEq

@[expose] public section

/-!
# Every earlier stored value is read at an earlier time

In dense time without a last moment, for a valid signal and `t ≥ 0`, every index `c ≤ cell t` is
`cell t'` for some time `0 ≤ t' ≤ t`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- An earlier value is read at an earlier time. -/
theorem PointSegmentSignal.exists_cell_le {T : Type} [LinearOrder T] [Zero T] [DenselyOrdered T]
    [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (t : T) (ht : 0 ≤ t) (c : ℕ)
    (hc : c ≤ s.cell t) : ∃ t', 0 ≤ t' ∧ t' ≤ t ∧ s.cell t' = c := by -- --- PROOF ---
  rcases hc.eq_or_lt with h | h
  · exact ⟨t, ht, le_rfl, h.symm⟩
  · -- a time reading the earlier value is not after `t`
    obtain ⟨t', ht', hct⟩ := s.exists_cell_eq hs c (lt_trans h (s.cell_lt hs t ht))
    refine ⟨t', ht', ?_, hct⟩
    by_contra hlt
    have := s.cell_mono hs t t' ht (not_le.1 hlt).le
    omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
