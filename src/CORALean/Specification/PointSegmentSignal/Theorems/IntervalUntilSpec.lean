module

public import CORALean.Specification.PointSegmentSignal.Operations.IntervalUntil
public import CORALean.Specification.Theorems.FoldlSetSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.SetSpec
public import CORALean.Specification.STLInterval.Theorems.ContainsPointZeroIff
public import CORALean.Specification.STLInterval.Theorems.FieldsAndRight
public import CORALean.Specification.STLInterval.Theorems.FieldsLeftClosure
public import CORALean.Specification.STLInterval.Theorems.LowerStlInterval
public import CORALean.Specification.STLInterval.Theorems.RepresentsaEmptySetIff
public import CORALean.Specification.STLInterval.Theorems.SetAnd
public import CORALean.Specification.STLInterval.Theorems.SetLeftClosure
public import CORALean.Specification.STLInterval.Theorems.SetMinus
public import CORALean.Specification.STLInterval.Theorems.SetRightClosure
public import CORALean.Specification.STLInterval.Theorems.SetUntilNoZero
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# The until of two lists of intervals

For lists of intervals with lower bounds `≥ 0`, `aux_intervalUntil` is a valid signal, `true` at `t
≥ 0` iff some interval of `lhsInt` and some `t'` in an interval of `rhsInt` have `t` in the left
closure and `t'` in the right closure of the first, and `t' - t` in the until interval, not `0`; or
`0` is in the until interval and `t` is in an interval of `rhsInt`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
/-- `aux_intervalUntil` is true exactly where a pair of intervals gives a witness. -/
theorem PointSegmentSignal.intervalUntil_spec (lhsInt rhsInt : List STLInterval) (U : STLInterval)
    (hL : ∀ I ∈ lhsInt, ∀ f, I.fieldsOf = some f → 0 ≤ f.lower)
    (hR : ∀ I ∈ rhsInt, ∀ f, I.fieldsOf = some f → 0 ≤ f.lower)
    (hU : ∀ f, U.fieldsOf = some f → 0 ≤ f.lower) :
    (PointSegmentSignal.intervalUntil lhsInt U rhsInt).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((PointSegmentSignal.intervalUntil lhsInt U rhsInt).at t = true ↔
        (∃ L ∈ lhsInt, ∃ R ∈ rhsInt, ∃ t' ∈ R.set, t' ∈ L.rightClosure.set ∧
          t ∈ L.leftClosure.set ∧ t' - t ∈ U.set ∧ t' ≠ t) ∨
        (0 ∈ U.set ∧ ∃ R ∈ rhsInt, t ∈ R.set)) := by -- --- PROOF ---
  -- the until interval without zero
  obtain ⟨hU'set, hU'nn⟩ := STLInterval.set_untilNoZero U _ hU rfl
  have h0U : U.containsPoint 0 0 ↔ (0 : ℝ) ∈ U.set := STLInterval.containsPoint_zero_iff U 0
  unfold PointSegmentSignal.intervalUntil
  dsimp only
  generalize (if U.containsPoint 0 0 then STLInterval.stlInterval 0 (U.supremum.value.getD 0)
    false U.supremum.closed else U) = U' at hU'set hU'nn ⊢
  -- the shifted interval of a pair of intervals, and its times
  let P : STLInterval → STLInterval → STLInterval := fun L R =>
    ((R.and_ L.rightClosure).minus U').and_ L.leftClosure
  have hP : ∀ L R : STLInterval, ∀ t : ℝ, t ∈ (P L R).set ↔ 0 ≤ t ∧ t ∈ L.leftClosure.set ∧
      ∃ t' ∈ R.set, t' ∈ L.rightClosure.set ∧ t' - t ∈ U.set ∧ t' ≠ t := by
    intro L R t
    show t ∈ (((R.and_ L.rightClosure).minus U').and_ L.leftClosure).set ↔ _
    rw [STLInterval.set_and_, STLInterval.set_minus, STLInterval.set_and_, hU'set]
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_sub, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨⟨a, ⟨ha1, ha2⟩, b, ⟨hb1, hb2⟩, hab⟩, h0⟩, hl⟩
      refine ⟨h0, hl, a, ha1, ha2, ?_, fun hat => hb2 (by linarith)⟩
      rwa [show a - t = b by linarith]
    · rintro ⟨h0, hl, a, ha1, ha2, hu, hne⟩
      exact ⟨⟨⟨a, ⟨ha1, ha2⟩, a - t, ⟨hu, fun h => hne (by linarith)⟩, by ring⟩, h0⟩, hl⟩
  have hPnn : ∀ L ∈ lhsInt, ∀ R, ∀ f, (P L R).fieldsOf = some f → 0 ≤ f.lower := fun L hL' R =>
    STLInterval.fields_and_right _ _ (STLInterval.fields_leftClosure L (hL L hL'))
  -- the step of the inner loop: set the shifted interval of a pair, unless it is empty
  let step : STLInterval → PointSegmentSignal ℝ → STLInterval → PointSegmentSignal ℝ :=
    fun L out R => if (P L R).representsa_ 0 .emptySet then out else out.set (P L R) true
  -- the inner step sets the shifted interval of a pair, unless it is empty
  have hstep : ∀ L ∈ lhsInt, ∀ (out : PointSegmentSignal ℝ) (R : STLInterval), out.IsValid →
      (step L out R).IsValid ∧
      ∀ t : ℝ, 0 ≤ t →
        (t ∈ (P L R).set → (step L out R).at t = true) ∧
        (t ∉ (P L R).set → (step L out R).at t = out.at t) := by
    intro L hL' out R hout
    by_cases he : (P L R).representsa_ 0 .emptySet
    · -- an empty interval has no time
      simp only [step, if_pos he]
      have := (STLInterval.representsa_emptySet_iff 0 _).1 he
      exact ⟨hout, fun t _ => ⟨fun h => absurd h (by rw [this]; simp), fun _ => trivial⟩⟩
    · simp only [step, if_neg he]
      exact PointSegmentSignal.set_spec out hout (P L R) (hPnn L hL' R) true
  -- all pairs of intervals, one left-hand side after the other
  have hinner : ∀ L ∈ lhsInt, ∀ (out : PointSegmentSignal ℝ), out.IsValid →
      (rhsInt.foldl (step L) out).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((∃ R ∈ rhsInt, t ∈ (P L R).set) → (rhsInt.foldl (step L) out).at t = true) ∧
      ((¬ ∃ R ∈ rhsInt, t ∈ (P L R).set) → (rhsInt.foldl (step L) out).at t = out.at t) :=
    fun L hL' out hout => List.foldl_set_spec (fun sig : PointSegmentSignal ℝ => sig.IsValid)
      (fun sig t => sig.at t) rhsInt (fun R => (P L R).set) true _
      (fun sig R _ hsig => hstep L hL' sig R hsig) out hout
  -- the signal that is false everywhere
  obtain ⟨hv0, h0⟩ := PointSegmentSignal.indicator_spec (STLInterval.stlInterval 0 ⊤ true true)
    (fun f hf => by rw [STLInterval.lower_stlInterval _ _ _ _ f hf]) false false
  obtain ⟨B, hBdef⟩ : ∃ B, B = lhsInt.foldl (fun out lhs => rhsInt.foldl (step lhs) out)
      (PointSegmentSignal.indicator (STLInterval.stlInterval 0 ⊤ true true) false false) :=
    ⟨_, rfl⟩
  obtain ⟨hvB, hB⟩ := List.foldl_set_spec (fun sig : PointSegmentSignal ℝ => sig.IsValid)
    (fun sig t => sig.at t) lhsInt (fun L => {t | ∃ R ∈ rhsInt, t ∈ (P L R).set}) true
    (fun out lhs => rhsInt.foldl (step lhs) out)
    (fun sig L hL' hsig => by
      obtain ⟨hv, h⟩ := hinner L hL' sig hsig
      exact ⟨hv, fun t ht => h t ht⟩) _ hv0
  rw [← hBdef] at hvB hB
  -- the signal `B` is true exactly where some pair gives a shifted interval
  have hBt : ∀ t : ℝ, 0 ≤ t → (B.at t = true ↔ ∃ L ∈ lhsInt, ∃ R ∈ rhsInt, t ∈ (P L R).set) := by
    intro t ht
    obtain ⟨b1, b2⟩ := hB t ht
    constructor
    · intro h
      by_contra hn
      have := b2 (fun ⟨L, hL', hh⟩ => hn ⟨L, hL', hh⟩)
      by_cases hm : t ∈ (STLInterval.stlInterval 0 ⊤ true true).set
      · rw [(h0 t ht).1 hm] at this; simp [this] at h
      · rw [(h0 t ht).2 hm] at this; simp [this] at h
    · rintro ⟨L, hL', hh⟩
      exact b1 ⟨L, hL', hh⟩
  rw [← hBdef]
  by_cases hc : U.containsPoint 0 0
  · -- the right-hand side intervals are set as well
    rw [if_pos hc]
    obtain ⟨hvF, hF⟩ := List.foldl_set_spec (fun sig : PointSegmentSignal ℝ => sig.IsValid)
      (fun sig t => sig.at t) rhsInt (fun R => R.set) true
      (fun out R => out.set R true)
      (fun sig R hR' hsig => PointSegmentSignal.set_spec sig hsig R (hR R hR') true) B hvB
    refine ⟨hvF, fun t ht => ?_⟩
    -- the right-hand side intervals are set last
    obtain ⟨f1, f2⟩ := hF t ht
    constructor
    · intro h
      by_cases hr : ∃ R ∈ rhsInt, t ∈ R.set
      · exact Or.inr ⟨h0U.1 hc, hr⟩
      · left
        have := (hBt t ht).1 (by rw [← f2 hr]; exact h)
        obtain ⟨L, hL', R, hR', hmem⟩ := this
        obtain ⟨-, hl, t', ht', hr', hu, hne⟩ := (hP L R t).1 hmem
        exact ⟨L, hL', R, hR', t', ht', hr', hl, hu, hne⟩
    · rintro (⟨L, hL', R, hR', t', ht', hr', hl, hu, hne⟩ | ⟨-, hr⟩)
      · by_cases hr : ∃ R ∈ rhsInt, t ∈ R.set
        · exact f1 hr
        · rw [f2 hr]
          exact (hBt t ht).2 ⟨L, hL', R, hR', (hP L R t).2 ⟨ht, hl, t', ht', hr', hu, hne⟩⟩
      · exact f1 hr
  · -- there is nothing more to set
    rw [if_neg hc]
    refine ⟨hvB, fun t ht => ?_⟩
    rw [hBt t ht]
    constructor
    · rintro ⟨L, hL', R, hR', hmem⟩
      obtain ⟨-, hl, t', ht', hr', hu, hne⟩ := (hP L R t).1 hmem
      exact Or.inl ⟨L, hL', R, hR', t', ht', hr', hl, hu, hne⟩
    · rintro (⟨L, hL', R, hR', t', ht', hr', hl, hu, hne⟩ | ⟨h, -⟩)
      · exact ⟨L, hL', R, hR', (hP L R t).2 ⟨ht, hl, t', ht', hr', hu, hne⟩⟩
      · exact absurd (h0U.2 h) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
