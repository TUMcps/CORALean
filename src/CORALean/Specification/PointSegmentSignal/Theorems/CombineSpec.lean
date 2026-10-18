module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Combine
public import CORALean.Specification.PointSegmentSignal.Theorems.AtBetween
public import CORALean.Specification.PointSegmentSignal.Theorems.AtLast
public import CORALean.Specification.PointSegmentSignal.Theorems.AtSnocEq
public import CORALean.Specification.PointSegmentSignal.Theorems.AtSnocGt
public import CORALean.Specification.PointSegmentSignal.Theorems.AtSnocLt
public import CORALean.Specification.PointSegmentSignal.Theorems.AtTimePoint
public import CORALean.Specification.PointSegmentSignal.Theorems.IsValidSnoc
public import CORALean.Specification.PointSegmentSignal.Theorems.ListLtOfPairwiseGetElemSucc
public import CORALean.Specification.PointSegmentSignal.Theorems.NonnegOfMemTimePoints
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Point-wise combination of signals is point-wise

The signal `combine(op,sig)(i)` is valid and, at every time `t ≥ 0`, has output `i` of `op`
applied to the values of the inputs at `t`. The proof runs the loop with an invariant: the output
built so far agrees with `op` at every time below the next unconsumed time point of the inputs.

With `¬` and `∧` as `op` this is their point-wise lift to Boolean signals of [1, Sec. 4.1].

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T] {ι : Type} [Fintype ι]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A valid signal has a time point. -/
theorem PointSegmentSignal.aux_isValid_pos (s : PointSegmentSignal T) (hs : s.IsValid) :
    1 ≤ s.length :=
  List.length_pos_iff.mpr hs.1

omit [LinearOrder T] in
/-- The time of an existing point is the point. -/
theorem PointSegmentSignal.aux_timeOrInf_of_get (s : PointSegmentSignal T) (idx : ℕ)
    (hidx : 1 ≤ idx) (a : T) (ha : s.timePoints[idx - 1]? = some a) :
    s.timeOrInf idx = (a : WithTop T) := by
  have hlt : idx - 1 < s.timePoints.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at ha; simp at ha
  have : idx ≤ s.length := by simp only [PointSegmentSignal.length]; omega
  simp [PointSegmentSignal.timeOrInf, this, List.getD_eq_getElem?_getD, ha]

omit [LinearOrder T] in
/-- Past the last point the time is `inf`. -/
theorem PointSegmentSignal.aux_timeOrInf_of_lt (s : PointSegmentSignal T) (idx : ℕ)
    (h : s.length < idx) : s.timeOrInf idx = ⊤ := by
  simp [PointSegmentSignal.timeOrInf, not_le.mpr h]

omit [LinearOrder T] [Zero T] in
/-- An index within the length has a time point. -/
theorem PointSegmentSignal.aux_exists_get (s : PointSegmentSignal T) (idx : ℕ) (hidx : 1 ≤ idx)
    (h : idx ≤ s.length) : ∃ a, s.timePoints[idx - 1]? = some a :=
  ⟨_, List.getElem?_eq_getElem (by simp only [PointSegmentSignal.length] at h; omega)⟩

/-- The next time `combine` will process: the smallest unconsumed time of the inputs. -/
def aux_loopTime (sig : ι → PointSegmentSignal T) (inIdx : ι → ℕ) : WithTop T :=
  Finset.univ.inf fun k => (sig k).timeOrInf (inIdx k)

/-- What the loop keeps: the output so far is right before the next time to process. -/
structure aux_LoopInv (op : (ι → Bool) → Bool) (sig : ι → PointSegmentSignal T)
    (fuel : ℕ) (inIdx : ι → ℕ) (tp : List T) (val : List Bool) : Prop where
  idx_ge : ∀ k, 1 ≤ inIdx k
  idx_le : ∀ k, inIdx k ≤ (sig k).length + 1
  fuel_ge : ∑ k, ((sig k).length + 1 - inIdx k) ≤ fuel
  prefix_ : (tp = [] ∧ val = [] ∧ ∀ k, inIdx k = 1) ∨ (PointSegmentSignal.mk tp val).IsValid
  consumed : ∀ k j a, j + 1 < inIdx k → (sig k).timePoints[j]? = some a →
    (a : WithTop T) < aux_loopTime sig inIdx
  last_lt : ∀ x ∈ tp, (x : WithTop T) < aux_loopTime sig inIdx
  agree : ∀ t : T, 0 ≤ t → (t : WithTop T) < aux_loopTime sig inIdx →
    (PointSegmentSignal.mk tp val).at t = op fun k => (sig k).at t

/-- When every input is consumed the invariant is the claim. -/
theorem aux_loopInv_final [Nonempty ι] (op : (ι → Bool) → Bool) (sig : ι → PointSegmentSignal T)
    (hv : ∀ k, (sig k).IsValid) (fuel : ℕ) (inIdx : ι → ℕ) (tp : List T)
    (val : List Bool) (inv : aux_LoopInv op sig fuel inIdx tp val)
    (hc : ¬ ∃ k, inIdx k ≤ (sig k).length) : -- --- STMT ---
    (PointSegmentSignal.mk tp val).IsValid ∧
      ∀ t : T, 0 ≤ t →
        (PointSegmentSignal.mk tp val).at t = op fun k => (sig k).at t := by -- --- PROOF ---
  have hN : aux_loopTime sig inIdx = ⊤ := by
    unfold aux_loopTime
    rw [Finset.inf_eq_top_iff]
    intro k _
    exact (sig k).aux_timeOrInf_of_lt _ (by simp only [not_exists, not_le] at hc; exact hc k)
  refine ⟨?_, fun t ht => inv.agree t ht (by rw [hN]; exact WithTop.coe_lt_top t)⟩
  rcases inv.prefix_ with ⟨-, -, h1⟩ | h
  · exfalso; apply hc
    refine ⟨(Classical.arbitrary ι), ?_⟩
    rw [h1]; exact (sig _).aux_isValid_pos (hv _)
  · exact h

/-- A time below a point's time is below the point. -/
theorem aux_lt_of_lt_timeOrInf (s : PointSegmentSignal T) (j : ℕ) (hj : 1 ≤ j) (t b : T)
    (hlt : (t : WithTop T) < s.timeOrInf j) (hb : s.timePoints[j - 1]? = some b) : t < b := by
  rw [s.aux_timeOrInf_of_get j hj b hb] at hlt
  exact_mod_cast hlt

/-- A signal consumed at this time contributes its point value. -/
theorem aux_pv_min (s : PointSegmentSignal T) (hs : s.IsValid) (idx : ℕ) (hidx : 1 ≤ idx)
    (τ : T) (h : s.timePoints[idx - 1]? = some τ) : s.pointValue idx = s.at τ := by
  have := s.at_timePoint hs (idx - 1) τ h
  rw [this, show idx - 1 + 1 = idx by omega]

/-- A signal not consumed at this time contributes the interval value before its next point. -/
theorem aux_pv_nonmin (s : PointSegmentSignal T) (hs : s.IsValid) (idx : ℕ) (hidx : 2 ≤ idx)
    (τ a : T) (ha : s.timePoints[idx - 2]? = some a) (haτ : a < τ)
    (h2 : ∀ b, s.timePoints[idx - 1]? = some b → τ < b) :
    s.precIntervalValue idx = s.at τ := by -- --- PROOF ---
  have := s.at_between hs (idx - 2) a τ ha haτ
    (by rw [show idx - 2 + 1 = idx - 1 by omega]; exact h2)
  rw [this]
  simp only [PointSegmentSignal.precIntervalValue, PointSegmentSignal.succIntervalValue]
  congr 1; omega

/-- A signal consumed at this time contributes its interval value afterwards. -/
theorem aux_iv_min (s : PointSegmentSignal T) (hs : s.IsValid) (idx : ℕ) (hidx : 1 ≤ idx)
    (τ t : T) (h : s.timePoints[idx - 1]? = some τ) (hτ : τ < t)
    (h2 : ∀ b, s.timePoints[idx]? = some b → t < b) : s.succIntervalValue idx = s.at t := by
  have := s.at_between hs (idx - 1) τ t h hτ (by rw [show idx - 1 + 1 = idx by omega]; exact h2)
  rw [this, show idx - 1 + 1 = idx by omega]

/-- A signal not consumed at this time keeps its interval value afterwards. -/
theorem aux_iv_nonmin (s : PointSegmentSignal T) (hs : s.IsValid) (idx : ℕ) (hidx : 2 ≤ idx)
    (t a : T) (ha : s.timePoints[idx - 2]? = some a) (hat : a < t)
    (h2 : ∀ b, s.timePoints[idx - 1]? = some b → t < b) :
    s.precIntervalValue idx = s.at t := aux_pv_nonmin s hs idx hidx t a ha hat h2

/-- At a pass of the loop, the consumed signals and the others are as the step needs. -/
theorem aux_loop_facts [Nonempty ι] (sig : ι → PointSegmentSignal T) (hv : ∀ k, (sig k).IsValid)
    (inIdx : ι → ℕ) (hge : ∀ k, 1 ≤ inIdx k)
    (hle : ∀ k, inIdx k ≤ (sig k).length + 1)
    (hcons : ∀ k j a, j + 1 < inIdx k → (sig k).timePoints[j]? = some a →
      (a : WithTop T) < aux_loopTime sig inIdx)
    (hc : ∃ k, inIdx k ≤ (sig k).length) : -- --- STMT ---
    ∃ τ : T, aux_loopTime sig inIdx = τ ∧
      (∀ k, (sig k).timeOrInf (inIdx k) = τ →
        inIdx k ≤ (sig k).length ∧ (sig k).timePoints[inIdx k - 1]? = some τ) ∧
      (∀ k, (sig k).timeOrInf (inIdx k) ≠ τ → 2 ≤ inIdx k ∧
        (τ : WithTop T) < (sig k).timeOrInf (inIdx k) ∧
        ∃ a, (sig k).timePoints[inIdx k - 2]? = some a ∧ a < τ) := by -- --- PROOF ---
  -- some input is unconsumed, so the next time is finite
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  obtain ⟨k1, hk1⟩ := hc
  have hfin : (sig k1).timeOrInf (inIdx k1) ≠ ⊤ := by
    obtain ⟨a, ha⟩ := (sig k1).aux_exists_get (inIdx k1) (hge k1) hk1
    rw [(sig k1).aux_timeOrInf_of_get _ (hge k1) a ha]; exact WithTop.coe_ne_top
  have hNle : aux_loopTime sig inIdx ≤ (sig k1).timeOrInf (inIdx k1) :=
    Finset.inf_le (f := fun k => (sig k).timeOrInf (inIdx k)) (Finset.mem_univ k1)
  have hNtop : aux_loopTime sig inIdx ≠ ⊤ := ne_top_of_le_ne_top hfin hNle
  obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.mp hNtop
  -- the consumed inputs have time `τ`; the others are later and have a previous point
  refine ⟨τ, hτ.symm, ?_, ?_⟩
  · intro k hk
    have hk' : inIdx k ≤ (sig k).length := by
      by_contra h
      rw [(sig k).aux_timeOrInf_of_lt _ (by omega)] at hk; exact WithTop.top_ne_coe hk
    obtain ⟨a, ha⟩ := (sig k).aux_exists_get _ (hge k) hk'
    rw [(sig k).aux_timeOrInf_of_get _ (hge k) a ha] at hk
    have : a = τ := WithTop.coe_injective hk
    exact ⟨hk', this ▸ ha⟩
  -- an input not consumed now has a point before and one after
  · intro k hk
    have hge2 : (τ : WithTop T) ≤ (sig k).timeOrInf (inIdx k) := by
      rw [hτ]; exact Finset.inf_le (f := fun k => (sig k).timeOrInf (inIdx k)) (Finset.mem_univ k)
    have hlt : (τ : WithTop T) < (sig k).timeOrInf (inIdx k) := lt_of_le_of_ne hge2 (Ne.symm hk)
-- an input not consumed now was consumed before: its first point is `0`
    have h2 : 2 ≤ inIdx k := by
      by_contra h
      have h1 : inIdx k = 1 := by have := hge k; omega
      have hl1 := (sig k).aux_isValid_pos (hv k)
      obtain ⟨a, ha⟩ := (sig k).aux_exists_get 1 le_rfl hl1
      have ha0 : a = 0 := by
        have := (hv k).2.2.1
        obtain ⟨b, l, hbl⟩ : ∃ b l, (sig k).timePoints = b :: l := by
          cases h : (sig k).timePoints with
          | nil => simp [h] at this
          | cons b l => exact ⟨b, l, rfl⟩
        rw [hbl] at this ha
        simp at this ha; rw [← ha, this]
      rw [h1, (sig k).aux_timeOrInf_of_get 1 le_rfl a ha, ha0] at hlt
-- every time is nonnegative
      have h0 : (0 : WithTop T) ≤ τ := by
        rw [hτ]
        refine Finset.le_inf fun j _ => ?_
        by_cases hj : inIdx j ≤ (sig j).length
        · obtain ⟨b, hb⟩ := (sig j).aux_exists_get _ (hge j) hj
          rw [(sig j).aux_timeOrInf_of_get _ (hge j) b hb]
          exact_mod_cast (sig j).nonneg_of_mem_timePoints (hv j) b (List.mem_of_getElem? hb)
        · rw [(sig j).aux_timeOrInf_of_lt _ (by omega)]; exact le_top
      exact absurd hlt (not_lt.mpr h0)
-- the previous point is the last consumed one
    have hlen : inIdx k - 2 < (sig k).length := by have := hle k; omega
    obtain ⟨a, ha⟩ := (sig k).aux_exists_get (inIdx k - 1) (by omega) (by omega)
    refine ⟨h2, hlt, a, ?_, ?_⟩
    · rw [show inIdx k - 1 - 1 = inIdx k - 2 by omega] at ha; exact ha
    · have ha' : (sig k).timePoints[inIdx k - 2]? = some a := by
        rw [show inIdx k - 1 - 1 = inIdx k - 2 by omega] at ha; exact ha
      have := hcons k (inIdx k - 2) a (by omega) ha'
      rw [← hτ] at this; exact_mod_cast this

/-- The next time is nonnegative. -/
theorem aux_zero_le_loopTime (sig : ι → PointSegmentSignal T) (hv : ∀ k, (sig k).IsValid)
    (inIdx : ι → ℕ) (hge : ∀ k, 1 ≤ inIdx k) :
    (0 : WithTop T) ≤ aux_loopTime sig inIdx := by -- --- PROOF ---
  refine Finset.le_inf fun j _ => ?_
  by_cases hj : inIdx j ≤ (sig j).length
  · obtain ⟨b, hb⟩ := (sig j).aux_exists_get _ (hge j) hj
    rw [(sig j).aux_timeOrInf_of_get _ (hge j) b hb]
    exact_mod_cast (sig j).nonneg_of_mem_timePoints (hv j) b (List.mem_of_getElem? hb)
  · rw [(sig j).aux_timeOrInf_of_lt _ (by omega)]; exact le_top

/-- One pass of the loop, with or without appending the point, keeps the invariant. -/
theorem aux_loopInv_step [Nonempty ι] (op : (ι → Bool) → Bool) (sig : ι → PointSegmentSignal T)
    (hv : ∀ k, (sig k).IsValid) (fuel : ℕ) (inIdx : ι → ℕ) (tp : List T)
    (val : List Bool) (inv : aux_LoopInv op sig (fuel + 1) inIdx tp val)
    (hc : ∃ k, inIdx k ≤ (sig k).length) : -- --- STMT ---
    let N := aux_loopTime sig inIdx
    let isMin : ι → Bool := fun k => decide ((sig k).timeOrInf (inIdx k) = N)
    let pv := op fun k =>
      if isMin k then (sig k).pointValue (inIdx k) else (sig k).precIntervalValue (inIdx k)
    let iv := op fun k =>
      if isMin k then (sig k).succIntervalValue (inIdx k) else (sig k).precIntervalValue (inIdx k)
    let inIdx' : ι → ℕ := fun k => if isMin k then inIdx k + 1 else inIdx k
    (tp ≠ [] ∧ pv = val.getD (val.length - 1) false ∧ pv = iv →
      aux_LoopInv op sig fuel inIdx' tp val) ∧
    (¬ (tp ≠ [] ∧ pv = val.getD (val.length - 1) false ∧ pv = iv) →
      aux_LoopInv op sig fuel inIdx' (tp ++ [N.untopD 0]) (val ++ [pv, iv])) := by -- --- PROOF ---
  -- name the smallest unconsumed time `τ` and the consumed inputs
  intro N isMin pv iv inIdx'
  obtain ⟨τ, hτ, hmin, hnon⟩ :=
    aux_loop_facts sig hv inIdx inv.idx_ge inv.idx_le inv.consumed hc
  have hN : N = τ := hτ
  have hmin' : ∀ k, isMin k = true ↔ (sig k).timeOrInf (inIdx k) = τ := by
    intro k; simp [isMin, hN]
  -- the new indices advance exactly the consumed inputs
  have hidx' : ∀ k, inIdx' k =
      if (sig k).timeOrInf (inIdx k) = τ then inIdx k + 1 else inIdx k := by
    intro k
    by_cases h : (sig k).timeOrInf (inIdx k) = τ
    · simp [inIdx', (hmin' k).mpr h, h]
    · have : isMin k = false := Bool.eq_false_iff.mpr fun hh => h ((hmin' k).mp hh)
      simp [inIdx', this, h]
  -- every new time is later than `τ`
  have htime' : ∀ k, (τ : WithTop T) < (sig k).timeOrInf (inIdx' k) := by
    intro k
    rw [hidx']
    by_cases h : (sig k).timeOrInf (inIdx k) = τ
    · rw [if_pos h]
      obtain ⟨hle', hget⟩ := hmin k h
      by_cases hl : inIdx k + 1 ≤ (sig k).length
      · obtain ⟨b, hb⟩ := (sig k).aux_exists_get (inIdx k + 1) (by omega) hl
        rw [(sig k).aux_timeOrInf_of_get _ (by omega) b hb]
        have : τ < b := List.lt_of_pairwise_getElem_succ (hv k).2.2.2.1 hget
          (by rw [show inIdx k - 1 + 1 = inIdx k + 1 - 1 by have := inv.idx_ge k; omega]; exact hb)
        exact_mod_cast this
      · rw [(sig k).aux_timeOrInf_of_lt _ (by omega)]; exact WithTop.coe_lt_top τ
    · rw [if_neg h]; exact (hnon k h).2.1
  have hN' : (τ : WithTop T) < aux_loopTime sig inIdx' :=
    (Finset.lt_inf_iff (WithTop.coe_lt_top τ)).mpr fun k _ => htime' k
  -- the point value is `op` of the signals' values at `τ`
  have hpv : pv = op fun k => (sig k).at τ := by
    show op (fun k => _) = _
    congr 1; funext k
    by_cases h : (sig k).timeOrInf (inIdx k) = τ
    · simp only [(hmin' k).mpr h, if_true]
      exact aux_pv_min (sig k) (hv k) (inIdx k) (inv.idx_ge k) τ (hmin k h).2
    · have : isMin k = false := Bool.eq_false_iff.mpr fun hh => h ((hmin' k).mp hh)
      simp only [this, Bool.false_eq_true, if_false]
      obtain ⟨h2, hlt, a, ha, haτ⟩ := hnon k h
      exact aux_pv_nonmin (sig k) (hv k) (inIdx k) h2 τ a ha haτ
        (fun b hb => aux_lt_of_lt_timeOrInf (sig k) (inIdx k) (inv.idx_ge k) τ b hlt hb)
  -- the interval value is `op` of their values anywhere in `(τ, next)`
  have hiv : ∀ t : T, τ < t → (t : WithTop T) < aux_loopTime sig inIdx' →
      iv = op fun k => (sig k).at t := by
    intro t hτt htN
    have hlt : ∀ k, (t : WithTop T) < (sig k).timeOrInf (inIdx' k) := fun k =>
      lt_of_lt_of_le htN
        (Finset.inf_le (f := fun k => (sig k).timeOrInf (inIdx' k)) (Finset.mem_univ k))
    show op (fun k => _) = _
    congr 1; funext k
    by_cases h : (sig k).timeOrInf (inIdx k) = τ
-- a consumed input: the value of its interval after the point
    · simp only [(hmin' k).mpr h, if_true]
      refine aux_iv_min (sig k) (hv k) (inIdx k) (inv.idx_ge k) τ t (hmin k h).2 hτt ?_
      intro b hb
      have := hlt k
      rw [hidx', if_pos h] at this
      exact aux_lt_of_lt_timeOrInf (sig k) (inIdx k + 1) (by omega) t b this (by simpa using hb)
-- an input not consumed: the value of its previous interval
    · have : isMin k = false := Bool.eq_false_iff.mpr fun hh => h ((hmin' k).mp hh)
      simp only [this, Bool.false_eq_true, if_false]
      obtain ⟨h2, hlt', a, ha, haτ⟩ := hnon k h
      refine aux_iv_nonmin (sig k) (hv k) (inIdx k) h2 t a ha (haτ.trans hτt) ?_
      intro b hb
      have := hlt k
      rw [hidx', if_neg h] at this
      exact aux_lt_of_lt_timeOrInf (sig k) (inIdx k) (inv.idx_ge k) t b this hb
  -- the indices stay within bounds and the fuel suffices
  have hge' : ∀ k, 1 ≤ inIdx' k := fun k => by
    have := inv.idx_ge k; rw [hidx']; split_ifs <;> omega
  have hle' : ∀ k, inIdx' k ≤ (sig k).length + 1 := fun k => by
    have := inv.idx_le k; rw [hidx']
    by_cases h : (sig k).timeOrInf (inIdx k) = τ
    · rw [if_pos h]; have := (hmin k h).1; omega
    · rw [if_neg h]; exact inv.idx_le k
  have hfuel : ∑ k, ((sig k).length + 1 - inIdx' k) ≤ fuel := by
    have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
    obtain ⟨k0, -, hk0⟩ := Finset.exists_mem_eq_inf Finset.univ hne
      (fun k => (sig k).timeOrInf (inIdx k))
    have hk0τ : (sig k0).timeOrInf (inIdx k0) = τ := by
      rw [← hk0]; exact hτ
    have hlt : ∑ k, ((sig k).length + 1 - inIdx' k) < ∑ k, ((sig k).length + 1 - inIdx k) := by
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨k0, Finset.mem_univ _, ?_⟩
      · rw [hidx']; split_ifs <;> omega
      · rw [hidx', if_pos hk0τ]; have := (hmin k0 hk0τ).1; have := inv.idx_ge k0; omega
    have := inv.fuel_ge
    omega
  -- the consumed points stay below the next time
  have hcons' : ∀ k j a, j + 1 < inIdx' k → (sig k).timePoints[j]? = some a →
      (a : WithTop T) < aux_loopTime sig inIdx' := by
    intro k j a hj ha
    refine lt_of_le_of_lt ?_ hN'
    rw [hidx'] at hj
    by_cases h : (sig k).timeOrInf (inIdx k) = τ
    · rw [if_pos h] at hj
      by_cases hj' : j + 1 < inIdx k
      · have := inv.consumed k j a hj' ha
        rw [hτ] at this; exact this.le
      · have hjeq : j = inIdx k - 1 := by omega
        have := (hmin k h).2
        rw [← hjeq, ha] at this
        have : a = τ := Option.some.inj this
        subst this; exact le_rfl
    · rw [if_neg h] at hj
      have := inv.consumed k j a hj ha
      rw [hτ] at this; exact this.le
  -- the output so far is below `τ` and right there
  have hlast : ∀ x ∈ tp, (x : WithTop T) < τ := fun x hx => by
    have := inv.last_lt x hx; rwa [hτ] at this
  have hagree_old : ∀ t : T, 0 ≤ t → t < τ →
      (PointSegmentSignal.mk tp val).at t = op fun k => (sig k).at t := fun t ht htτ =>
    inv.agree t ht (by rw [hτ]; exact_mod_cast htτ)
  have hlen : val.length = 2 * tp.length := by
    rcases inv.prefix_ with ⟨rfl, rfl, -⟩ | h
    · rfl
    · exact h.2.1
  -- an empty output means the first pass, whose time is `0`
  have hτ0 : tp = [] → τ = 0 := by
    intro htp
    rcases inv.prefix_ with ⟨-, -, h1⟩ | h
    · have hk0 : (sig (Classical.arbitrary ι)).timeOrInf (inIdx (Classical.arbitrary ι)) =
          ((0 : T) : WithTop T) := by
        rw [h1]
        refine (sig (Classical.arbitrary ι)).aux_timeOrInf_of_get 1 le_rfl 0 ?_
        have := (hv (Classical.arbitrary ι)).2.2.1
        obtain ⟨b, l, hbl⟩ : ∃ b l, (sig (Classical.arbitrary ι)).timePoints = b :: l := by
          cases h : (sig (Classical.arbitrary ι)).timePoints with
          | nil => simp [h] at this
          | cons b l => exact ⟨b, l, rfl⟩
        rw [hbl] at this ⊢
        simpa using this
-- so `τ ≤ 0`, and `τ` is nonnegative
      have h1' : (τ : WithTop T) ≤ ((0 : T) : WithTop T) := by
        rw [← hk0, ← hτ]
        exact Finset.inf_le (f := fun k => (sig k).timeOrInf (inIdx k)) (Finset.mem_univ _)
      have h2' : (0 : WithTop T) ≤ τ := by
        have := aux_zero_le_loopTime sig hv inIdx inv.idx_ge
        rwa [hτ] at this
      exact le_antisymm (by exact_mod_cast h1') (by exact_mod_cast h2')
    · exact absurd htp h.1
  -- appending `τ` leaves the values below it as they were
  have hat_snoc_lt : ∀ t : T, 0 ≤ t → t < τ → ∀ τ' : T, τ' = τ →
      (PointSegmentSignal.mk (tp ++ [τ']) (val ++ [pv, iv])).at t =
        op fun k => (sig k).at t := by
    intro t ht htτ τ' hτ'
    subst hτ'
    have hne : tp ≠ [] := fun h => by
      have := hτ0 h; subst this; exact absurd htτ (not_lt.mpr ht)
    rw [PointSegmentSignal.at_snoc_lt tp val τ' pv iv hlen hne t htτ]
    exact hagree_old t ht htτ
  -- the point is dropped when it repeats the interval before and after
  constructor
  · rintro ⟨hne, h1, h2⟩
    refine ⟨hge', hle', hfuel, ?_, ?_, ?_, ?_⟩
    · rcases inv.prefix_ with ⟨h, -, -⟩ | h
      · exact absurd h hne
      · exact Or.inr h
    · exact hcons'
    · intro x hx; exact (hlast x hx).trans hN'
    · intro t ht htN
      by_cases htτ : t < τ
      · exact hagree_old t ht htτ
      · have hge : τ ≤ t := not_lt.mp htτ
        have hlt : ∀ x ∈ tp, x < t := fun x hx => by
          have := hlast x hx; exact lt_of_lt_of_le (by exact_mod_cast this) hge
        rw [PointSegmentSignal.at_last tp val hlen hne t hlt, ← h1]
        rcases hge.lt_or_eq with hgt | heq
        · rw [h2]; exact hiv t hgt htN
        · subst heq; exact hpv
  -- otherwise the point is appended
  · intro hnot
    have hu : N.untopD 0 = τ := by rw [hN]; rfl
    rw [hu]
    refine ⟨hge', hle', hfuel, ?_, hcons', ?_, ?_⟩
    · refine Or.inr (PointSegmentSignal.isValid_snoc tp val τ pv iv ?_)
      by_cases htp : tp = []
      · exact Or.inl ⟨htp, by rw [htp] at hlen; simpa using hlen, hτ0 htp⟩
      · rcases inv.prefix_ with ⟨h, -, -⟩ | hvalid
        · exact absurd h htp
        · refine Or.inr ⟨hvalid, fun x hx => ?_, fun hc' => hnot ⟨htp, hc'.1, hc'.2⟩⟩
          have := hlast x hx; exact_mod_cast this
-- all output times stay below the next time
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hlast x hx).trans hN'
      · rw [List.mem_singleton.mp hx]; exact hN'
-- the output agrees below, at and above `τ`
    · intro t ht htN
      have hlt : ∀ x ∈ tp, x < τ := fun x hx => by have := hlast x hx; exact_mod_cast this
      rcases lt_trichotomy t τ with h | h | h
      · exact hat_snoc_lt t ht h τ rfl
      · subst h
        rw [PointSegmentSignal.at_snoc_eq tp val t pv iv hlen hlt]; exact hpv
      · rw [PointSegmentSignal.at_snoc_gt tp val τ pv iv hlen hlt t h]; exact hiv t h htN

/-- The loop from any state satisfying the invariant ends in the claim. -/
theorem aux_combineLoop_spec [Nonempty ι] (op : (ι → Bool) → Bool) (sig : ι → PointSegmentSignal T)
    (hv : ∀ k, (sig k).IsValid) (fuel : ℕ) : -- --- STMT ---
    ∀ (inIdx : ι → ℕ) (tp : List T) (val : List Bool),
      aux_LoopInv op sig fuel inIdx tp val →
      (PointSegmentSignal.mk (PointSegmentSignal.combineLoop op sig fuel inIdx tp val).1
        (PointSegmentSignal.combineLoop op sig fuel inIdx tp val).2).IsValid ∧
      ∀ t : T, 0 ≤ t → (PointSegmentSignal.mk
        (PointSegmentSignal.combineLoop op sig fuel inIdx tp val).1
        (PointSegmentSignal.combineLoop op sig fuel inIdx tp val).2).at t =
          op fun k => (sig k).at t := by -- --- PROOF ---
  -- at time `0` no time is below the first point
  induction fuel with
  | zero =>
    intro inIdx tp val inv
-- no fuel left: every input is consumed
    have hc : ¬ ∃ k, inIdx k ≤ (sig k).length := by
      rintro ⟨k, hk⟩
      have h1 : ∑ k, ((sig k).length + 1 - inIdx k) = 0 := Nat.le_zero.mp inv.fuel_ge
      have h2 := (Finset.sum_eq_zero_iff.mp h1) k (Finset.mem_univ k)
      omega
    simp only [PointSegmentSignal.combineLoop]
    exact aux_loopInv_final op sig hv 0 inIdx tp val inv hc
  | succ fuel ih =>
    intro inIdx tp val inv
-- one pass, then the induction hypothesis
    by_cases hc : ∃ k, inIdx k ≤ (sig k).length
    · obtain ⟨hskip, happ⟩ := aux_loopInv_step op sig hv fuel inIdx tp val inv hc
      rw [PointSegmentSignal.combineLoop, if_pos hc]
      dsimp only
      split_ifs with hs
      · exact ih _ _ _ (hskip hs)
      · exact ih _ _ _ (happ hs)
    · rw [PointSegmentSignal.combineLoop, if_neg hc]
      exact aux_loopInv_final op sig hv _ inIdx tp val inv hc


/-- The invariant holds at the start. -/
theorem aux_loopInv_init [Nonempty ι] (op : (ι → Bool) → Bool) (sig : ι → PointSegmentSignal T)
    (hv : ∀ k, (sig k).IsValid) :
    aux_LoopInv op sig (∑ k, (sig k).length + 1) (fun _ => 1) [] [] := by -- --- PROOF ---
  have hN : aux_loopTime sig (fun _ => 1) ≤ ((0 : T) : WithTop T) := by
    have hk0 : (sig (Classical.arbitrary ι)).timeOrInf 1 = ((0 : T) : WithTop T) := by
      refine (sig (Classical.arbitrary ι)).aux_timeOrInf_of_get 1 le_rfl 0 ?_
      have := (hv (Classical.arbitrary ι)).2.2.1
      obtain ⟨b, l, hbl⟩ : ∃ b l, (sig (Classical.arbitrary ι)).timePoints = b :: l := by
        cases h : (sig (Classical.arbitrary ι)).timePoints with
        | nil => simp [h] at this
        | cons b l => exact ⟨b, l, rfl⟩
      rw [hbl] at this ⊢
      simpa using this
    rw [← hk0]
    exact Finset.inf_le (f := fun k => (sig k).timeOrInf 1) (Finset.mem_univ _)
  refine ⟨fun _ => le_rfl, fun k => by omega, ?_, Or.inl ⟨rfl, rfl, fun _ => rfl⟩, ?_, ?_,
    ?_⟩
  · refine le_trans (Finset.sum_le_sum fun k _ => ?_) (Nat.le_succ _)
    omega
  · intro k j a hj; omega
  · intro x hx; simp at hx
  · intro t ht htN
    exact absurd (lt_of_lt_of_le htN hN) (not_lt.mpr (by exact_mod_cast ht))


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.combine_spec {T : Type} [LinearOrder T] [Zero T] {ι κ : Type}
    [Fintype ι] [Nonempty ι]
    (op : (ι → Bool) → κ → Bool) (sig : ι → PointSegmentSignal T)
    (hv : ∀ k, (sig k).IsValid) (i : κ) : -- --- STMT ---
    (PointSegmentSignal.combine op sig i).IsValid ∧ ∀ t : T, 0 ≤ t →
      (PointSegmentSignal.combine op sig i).at t
        = op (fun k => (sig k).at t) i := by -- --- PROOF ---
  have hinit := aux_loopInv_init (fun a => op a i) sig hv
  exact aux_combineLoop_spec (fun a => op a i) sig hv _ _ _ _ hinit

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
