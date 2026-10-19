module

public import CORALean.Specification.PointSegmentSignal.Operations.FindLast
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellGeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLt
public import CORALean.Specification.PointSegmentSignal.Theorems.ExistsCellEq
public import CORALean.Specification.PointSegmentSignal.Theorems.MemMatlabFind
public import CORALean.Specification.PointSegmentSignal.Theorems.NonnegOfMemTimePoints
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Interval.Set.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.AtEqCell
public import CORALean.Specification.PointSegmentSignal.Theorems.PrecTimeAtValIdxSucc
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfLt
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfGe
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# The end of the last stretch with a value

In dense time without a last moment, for a valid signal, `findLast(obj,value)` is the least upper
bound of the times `t ≥ 0` at which the signal has the value `value`, and `inclusive` says whether
some such time is that bound. If the signal never has the value, it is `0` and not inclusive.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `findLast` is the supremum of the times with the value, and whether it is attained. -/
theorem PointSegmentSignal.findLast_spec {T : Type} [LinearOrder T] [Zero T] [DenselyOrdered T]
    [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (value : Bool) : -- --- CONCL ---
    ((∃ t : T, 0 ≤ t ∧ s.at t = value) →
      IsLUB {x : WithTop T | ∃ t : T, 0 ≤ t ∧ s.at t = value ∧ (t : WithTop T) = x}
        (s.findLast value).1 ∧
      ((s.findLast value).2 = true ↔
        ∃ t : T, 0 ≤ t ∧ s.at t = value ∧ (t : WithTop T) = (s.findLast value).1)) ∧
    ((¬ ∃ t : T, 0 ≤ t ∧ s.at t = value) →
      s.findLast value = (((0 : T) : WithTop T), false)) := by -- --- PROOF ---
  have hlen := hs.2.1
  have hsort := List.pairwise_matlabFind (· == value) s.values
  -- the indices found: those whose value is `value`
  have hmem : ∀ j, j ∈ List.matlabFind (· == value) s.values ↔
      1 ≤ j ∧ ∃ h : j - 1 < s.values.length, s.values[j - 1] = value := by
    intro j; rw [List.mem_matlabFind]; simp
  have hmem' : ∀ m, m + 1 ∈ List.matlabFind (· == value) s.values ↔
      ∃ h : m < s.values.length, s.values[m] = value := by
    intro m; rw [hmem]; simp
  have hget : ∀ m (h : m < s.values.length), s.values[m] = s.values.getD m false := fun m h => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  refine ⟨?_, fun hne => ?_⟩
  · rintro ⟨t₀, ht₀, hv₀⟩
    -- the last index found, and the largest value index with the value
    have hm0 : s.cell t₀ + 1 ∈ List.matlabFind (· == value) s.values :=
      (hmem' _).2 ⟨s.cell_lt hs t₀ ht₀, by
        rw [hget _ (s.cell_lt hs t₀ ht₀), ← PointSegmentSignal.at_eq_cell, hv₀]⟩
    obtain ⟨i, hi⟩ : ∃ i, (List.matlabFind (· == value) s.values).getLast? = some i := by
      cases h : (List.matlabFind (· == value) s.values).getLast? with
      | none => exact absurd hm0 (by rw [List.getLast?_eq_none_iff.1 h]; simp)
      | some i => exact ⟨i, rfl⟩
    have hfl : s.findLast value = s.succTimeAtValIdx i := by simp [PointSegmentSignal.findLast, hi]
    have hmax : ∀ j ∈ List.matlabFind (· == value) s.values, j ≤ i := by
      obtain ⟨L', hL'⟩ := List.getLast?_eq_some_iff.1 hi
      intro j hj
      rw [hL'] at hj hsort
      rcases List.mem_append.1 hj with hj' | hj'
      · exact ((List.pairwise_append.1 hsort).2.2 j hj' i (by simp)).le
      · simp at hj'; omega
    obtain ⟨hi1, hi2, hi3⟩ := (hmem i).1 (List.mem_of_getLast? hi)
    -- every time with the value reads a value index at most `i - 1`
    have hUB : ∀ t : T, 0 ≤ t → s.at t = value → s.cell t ≤ i - 1 := fun t ht hv => by
      have hc := s.cell_lt hs t ht
      have := hmax (s.cell t + 1) ((hmem' _).2 ⟨hc, by
        rw [hget _ hc, ← PointSegmentSignal.at_eq_cell, hv]⟩)
      omega
    rw [hfl]
    -- the value index `b`, the last one with the value
    obtain ⟨b, rfl⟩ : ∃ b, i = b + 1 := ⟨i - 1, by omega⟩
    have hb : b < s.values.length := by simpa using hi2
    have hvb : s.values.getD b false = value := by rw [← hget _ hb]; simpa using hi3
    have hUB' : ∀ t : T, 0 ≤ t → s.at t = value → s.cell t ≤ b := fun t ht hv => by
      simpa using hUB t ht hv
    have hcl := fun t ht => s.cell_le_iff hs t ht b hb
    -- a time `t₀'` reading the value `b`, and what that says of the bounds around it
    obtain ⟨t₀', ht₀', hc₀'⟩ := s.exists_cell_eq hs b hb
    have hv₀' : s.at t₀' = value := by rw [PointSegmentSignal.at_eq_cell, hc₀']; exact hvb
    have hk : b / 2 < s.timePoints.length := by omega
    have hpre := s.precTimeAtValIdx_succ b hk
    have hge₀ := (s.cell_ge_iff hs t₀' ht₀' b hb).1 (le_of_eq hc₀'.symm)
    have hle₀ := (s.cell_le_iff hs t₀' ht₀' b hb).1 (le_of_eq hc₀')
    rw [hpre] at hge₀
    -- the end of the value is an upper bound of the times with the value
    have hub : ∀ x ∈ {x : WithTop T | ∃ t : T, 0 ≤ t ∧ s.at t = value ∧ (t : WithTop T) = x},
        x ≤ (s.succTimeAtValIdx (b + 1)).1 := by
      rintro x ⟨t, ht, hv, rfl⟩
      rcases (hcl t ht).1 (hUB' t ht hv) with h | ⟨-, h⟩
      · exact h.le
      · exact h.le
    rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1
    · -- an even index is a point value: the end is that time point, which has the value
      have hsucc := s.succTimeAtValIdx_of_lt b (by omega)
      have hidx : (b + 1) / 2 = b / 2 := by omega
      simp only [hidx] at hsucc
      have hflag : (s.succTimeAtValIdx (b + 1)).2 = true := by simp [hsucc, hb0]
      have ht₀eq : t₀' = s.timePoints[b / 2] := by
        simp only [hsucc, hb0, decide_true, true_and, WithTop.coe_lt_coe, WithTop.coe_inj] at hle₀
        simp only [hb0, decide_true, true_and] at hge₀
        rcases hge₀ with h | h <;> rcases hle₀ with h' | h'
        · exact absurd h' (not_lt.2 h.le)
        · exact h'
        · exact h
        · exact h
      have htu : (s.succTimeAtValIdx (b + 1)).1 = ((t₀' : T) : WithTop T) := by
        rw [hsucc]
        exact congrArg (fun x : T => (x : WithTop T)) ht₀eq.symm
      refine ⟨⟨hub, fun u hu => ?_⟩, ⟨fun _ => ⟨t₀', ht₀', hv₀', htu.symm⟩, fun _ => hflag⟩⟩
      rw [htu]
      exact hu ⟨t₀', ht₀', hv₀', rfl⟩
    · -- an odd index is an interval value: the end is not attained, and approached from inside
      have hflag : (s.succTimeAtValIdx (b + 1)).2 = false := by
        by_cases hlt : (b + 1) / 2 < s.timePoints.length
        · simp [s.succTimeAtValIdx_of_lt b hlt, hb1]
        · simp [s.succTimeAtValIdx_of_ge b (not_lt.1 hlt), hb1]
      -- the point time before the value, and the time `t₀'` between it and the end
      have hge₁ : s.timePoints[b / 2] < t₀' := by
        rcases hge₀ with h | ⟨h, -⟩
        · exact h
        · simp [hb1] at h
      have hle₁ : ((t₀' : T) : WithTop T) < (s.succTimeAtValIdx (b + 1)).1 := by
        rcases hle₀ with h | ⟨h, -⟩
        · exact h
        · simp [hflag] at h
      refine ⟨⟨hub, fun u hu => ?_⟩, ⟨fun h => by simp [hflag] at h, ?_⟩⟩
      · -- an upper bound below the end would be exceeded by a time reading the value
        by_contra hlt
        have hlt' := not_le.1 hlt
        induction u using WithTop.recTopCoe with
        | top => exact absurd hlt' (not_lt.2 le_top)
        -- a finite upper bound below the end
        | coe u₀ =>
          have hmax : (((max u₀ s.timePoints[b / 2] : T)) : WithTop T) <
              (s.succTimeAtValIdx (b + 1)).1 := by
            rcases le_total u₀ s.timePoints[b / 2] with h | h
            · rw [max_eq_right h]; exact lt_trans (WithTop.coe_lt_coe.2 hge₁) hle₁
            · rw [max_eq_left h]; exact hlt'
          obtain ⟨t₂, ht₂1, ht₂2⟩ : ∃ t₂ : T, max u₀ s.timePoints[b / 2] < t₂ ∧
              (t₂ : WithTop T) < (s.succTimeAtValIdx (b + 1)).1 := by
            generalize (s.succTimeAtValIdx (b + 1)).1 = w at hmax
            induction w using WithTop.recTopCoe with
            | top =>
              obtain ⟨t, ht⟩ := exists_gt (max u₀ s.timePoints[b / 2])
              exact ⟨t, ht, WithTop.coe_lt_top _⟩
            | coe w₀ =>
              obtain ⟨t, ht1, ht2⟩ := exists_between (WithTop.coe_lt_coe.1 hmax)
              exact ⟨t, ht1, WithTop.coe_lt_coe.2 ht2⟩
          -- a time reading the value, above that bound and below the end
          have ha0 := PointSegmentSignal.nonneg_of_mem_timePoints s hs _ (List.getElem_mem hk)
          have ht₂0 : 0 ≤ t₂ := ha0.trans ((le_max_right _ _).trans ht₂1.le)
          have hc₂ : s.cell t₂ = b := le_antisymm ((hcl t₂ ht₂0).2 (Or.inl ht₂2))
            ((s.cell_ge_iff hs t₂ ht₂0 b hb).2 (Or.inl (by
              rw [hpre]; exact lt_of_le_of_lt (le_max_right _ _) ht₂1)))
          have hv₂ : s.at t₂ = value := by rw [PointSegmentSignal.at_eq_cell, hc₂]; exact hvb
          have := hu ⟨t₂, ht₂0, hv₂, rfl⟩
          exact absurd (WithTop.coe_le_coe.1 this)
            (not_le.2 (lt_of_le_of_lt (le_max_left _ _) ht₂1))
      · -- the end is not attained
        rintro ⟨t, ht0, hv, hte⟩
        rcases (hcl t ht0).1 (hUB' t ht0 hv) with h | ⟨h, -⟩
        · exact absurd hte (ne_of_lt h)
        · simp [hflag] at h
  · -- no time has the value, so no value does
    have hnil : List.matlabFind (· == value) s.values = [] := by
      refine List.eq_nil_iff_forall_not_mem.2 fun j hj => ?_
      obtain ⟨h1, h2, h3⟩ := (hmem j).1 hj
      obtain ⟨t, ht0, hct⟩ := s.exists_cell_eq hs (j - 1) h2
      exact hne ⟨t, ht0, by rw [PointSegmentSignal.at_eq_cell, hct, ← hget _ h2, h3]⟩
    simp [PointSegmentSignal.findLast, hnil]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
