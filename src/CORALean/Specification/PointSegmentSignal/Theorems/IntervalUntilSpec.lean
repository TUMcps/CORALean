module

public import CORALean.Specification.PointSegmentSignal.Operations.IntervalUntil
public import CORALean.Specification.Theorems.FoldlSetSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.SetSpec
public import CORALean.Specification.STLInterval.Theorems.ContainsPointZeroIff
public import CORALean.Specification.STLInterval.Theorems.RepresentsaEmptySetIff
public import CORALean.Specification.STLInterval.Theorems.SetAnd
public import CORALean.Specification.STLInterval.Theorems.SetLeftClosure
public import CORALean.Specification.STLInterval.Theorems.SetMinus
public import CORALean.Specification.STLInterval.Theorems.SetRightClosure
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.Supremum
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# The until of two lists of intervals

For lists of intervals with lower bounds `≥ 0`, `aux_intervalUntil` is a valid signal, `true` at `t
≥ 0` iff some interval of `lhsInt` and some `t'` in an interval of `rhsInt` have `t` in the left
closure and `t'` in the right closure of the first, and `t' - t` in the until interval, not `0`; or
`0` is in the until interval and `t` is in an interval of `rhsInt`.

With one interval on each side this is the unitary until `t ∈ I₁ ∪ I₂` of [1, Eq. 1], which
[1, Lemma 1] shows to be the until.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Classical in
/-- `untilIntNoZero` denotes the times of the until interval except `0`. -/
private theorem STLInterval.aux_set_untilNoZero (U U' : STLInterval ℝ)
    (hU' : U' = if U.containsPoint 0 0 then
      STLInterval.stlInterval (0 : ℝ) (U.supremum.value.getD 0) false U.supremum.closed (by simp)
      else U)
    : -- --- CONCL ---
    U'.set = U.set \ {0} := by -- --- PROOF ---
  by_cases h : U.containsPoint 0 0
  · -- `0` is in the interval, so the interval starts at `0`, closed
    have h0 := (STLInterval.containsPoint_zero_iff U 0).1 h
    rw [hU', if_pos h]
    cases U with
    | empty => exact absurd h0 (by simp [STLInterval.set])
    | nonempty l u lc rc b c hl =>
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq, EReal.coe_zero,
        Float.toReal_real, EReal.coe_lt_coe_iff, EReal.coe_eq_coe_iff] at h0
      simp only [Float.toReal_real] at hl
      have hl0 : l = 0 := by
        rcases h0.1 with h' | ⟨-, h'⟩
        · exact absurd hl (not_le.2 h')
        · exact h'
      have hlc : lc = true := by
        rcases h0.1 with h' | ⟨h', -⟩
        · exact absurd hl (not_le.2 h')
        · exact h'
      -- the sets agree except at `0`
      simp only [STLInterval.supremum, Option.getD_some]
      rw [STLInterval.set_stlInterval]
      ext t
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq, Set.mem_sdiff,
        Set.mem_singleton_iff, hl0, hlc]
      constructor
      · rintro ⟨h1 | ⟨h1, -⟩, h2⟩
        · exact ⟨⟨Or.inl h1, h2⟩, fun e => by simp [e] at h1⟩
        · exact absurd h1 (by simp)
      · rintro ⟨⟨h1 | ⟨-, h1⟩, h2⟩, h3⟩
        · exact ⟨Or.inl h1, h2⟩
        · exact absurd (by exact_mod_cast h1.symm) h3
  · -- `0` is not in the interval
    have h0 : (0 : ℝ) ∉ U.set := fun h' => h ((STLInterval.containsPoint_zero_iff U 0).2 h')
    rw [hU', if_neg h]
    exact (Set.sdiff_singleton_eq_self h0).symm

end


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
/-- `aux_intervalUntil` is true exactly where a pair of intervals gives a witness. -/
theorem PointSegmentSignal.intervalUntil_spec (lhsInt rhsInt : List (STLInterval ℝ))
    (U : STLInterval ℝ) : -- --- CONCL ---
    (PointSegmentSignal.intervalUntil lhsInt U rhsInt).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((PointSegmentSignal.intervalUntil lhsInt U rhsInt).at t = true ↔
        (∃ L ∈ lhsInt, ∃ R ∈ rhsInt, ∃ t' ∈ R.set, t' ∈ L.rightClosure.set ∧
          t ∈ L.leftClosure.set ∧ t' - t ∈ U.set ∧ t' ≠ t) ∨
        (0 ∈ U.set ∧ ∃ R ∈ rhsInt, t ∈ R.set)) := by -- --- PROOF ---
  -- the until interval without zero
  have hU'set := STLInterval.aux_set_untilNoZero U _ rfl
  have h0U : U.containsPoint 0 0 ↔ (0 : ℝ) ∈ U.set := STLInterval.containsPoint_zero_iff U 0
  unfold PointSegmentSignal.intervalUntil
  dsimp only
  generalize (if U.containsPoint 0 0 then STLInterval.stlInterval (0 : ℝ)
    (U.supremum.value.getD 0) false U.supremum.closed (by simp) else U) = U' at hU'set ⊢
  -- the shifted interval of a pair of intervals, and its times
  let P : STLInterval ℝ → STLInterval ℝ → STLInterval ℝ := fun L R =>
    ((R.and_ L.rightClosure).minus U').and_ L.leftClosure
  have hP : ∀ L R : STLInterval ℝ, ∀ t : ℝ, t ∈ (P L R).set ↔ 0 ≤ t ∧ t ∈ L.leftClosure.set ∧
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
  -- the step of the inner loop: set the shifted interval of a pair, unless it is empty
  let step : STLInterval ℝ → PointSegmentSignal ℝ → STLInterval ℝ → PointSegmentSignal ℝ :=
    fun L out R => if (P L R).representsa_ 0 .emptySet then out else out.set (P L R) true
  -- the inner step sets the shifted interval of a pair, unless it is empty
  have hstep : ∀ L ∈ lhsInt, ∀ (out : PointSegmentSignal ℝ) (R : STLInterval ℝ), out.IsValid →
      (step L out R).IsValid ∧
      ∀ t : ℝ, 0 ≤ t →
        (t ∈ (P L R).set → (step L out R).at t = true) ∧
        (t ∉ (P L R).set → (step L out R).at t = out.at t) := by
    intro L _ out R hout
    by_cases he : (P L R).representsa_ 0 .emptySet
    · -- an empty interval has no time
      simp only [step, if_pos he]
      have := (STLInterval.representsa_emptySet_iff 0 _).1 he
      exact ⟨hout, fun t _ => ⟨fun h => absurd h (by rw [this]; simp), fun _ => trivial⟩⟩
    · simp only [step, if_neg he]
      exact PointSegmentSignal.set_spec out hout (P L R) true
  -- all pairs of intervals, one left-hand side after the other
  have hinner : ∀ L ∈ lhsInt, ∀ (out : PointSegmentSignal ℝ), out.IsValid →
      (rhsInt.foldl (step L) out).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((∃ R ∈ rhsInt, t ∈ (P L R).set) → (rhsInt.foldl (step L) out).at t = true) ∧
      ((¬ ∃ R ∈ rhsInt, t ∈ (P L R).set) → (rhsInt.foldl (step L) out).at t = out.at t) :=
    fun L hL' out hout => List.foldl_set_spec (fun sig : PointSegmentSignal ℝ => sig.IsValid)
      (fun sig t => sig.at t) rhsInt (fun R => (P L R).set) true _
      (fun sig R _ hsig => hstep L hL' sig R hsig) out hout
  -- the signal that is false everywhere
  obtain ⟨hv0, h0⟩ :=
    PointSegmentSignal.indicator_spec (STLInterval.stlInterval (0 : ℝ) ⊤ true true
        (by simp)) false false
  obtain ⟨B, hBdef⟩ : ∃ B, B = lhsInt.foldl (fun out lhs => rhsInt.foldl (step lhs) out)
      (PointSegmentSignal.indicator (STLInterval.stlInterval (0 : ℝ) ⊤ true true
          (by simp)) false false) :=
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
      by_cases hm : t ∈ (STLInterval.stlInterval (0 : ℝ) ⊤ true true (by simp)).set
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
      (fun sig R _ hsig => PointSegmentSignal.set_spec sig hsig R true) B hvB
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
