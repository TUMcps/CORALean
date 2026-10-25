module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.ConclusiveInterval
public import CORALean.Specification.FourValuedSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CutAtFirstFallingEdgeAt
public import CORALean.Specification.PointSegmentSignal.Theorems.CutAtFirstFallingEdgeSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.FindLastSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.NotAt
public import CORALean.Specification.PointSegmentSignal.Theorems.NotIsValid
public import CORALean.Specification.PointSegmentSignal.Theorems.SetSpec
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.SetStlIntervalBounds

@[expose] public section

/-!
# The initial conclusive interval of a four-valued signal

For a valid four-valued signal and an `ignore` interval with lower bound `≥ 0`, a time `t` is in
`conclusiveInterval(obj,ignore)` iff `t ≥ 0` and at every time up to `t` the signal is conclusive or
the time is in `ignore`: the interval is the longest initial stretch with that property, closed at
its end if the property holds there.

This is `ConclusiveInterval` in line 11 of [1, Alg. 2], with `ignore` the irrelevant prefix `n.irr`.

## Inputs
* `obj` – four-valued signal
* `ignore` – interval to disregard
* `t` – time

## Hypotheses
* `hobj` – the signal is valid

## Conclusion
* a time is in the interval iff no earlier time is inconclusive

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The conclusive interval is the longest initial stretch without inconclusive times. -/
theorem FourValuedSignal.conclusiveInterval_spec (obj : FourValuedSignal ℝ) (hobj : obj.IsValid)
    (ignore : STLInterval ℝ) (t : ℝ) : -- --- CONCL ---
    t ∈ (obj.conclusiveInterval ignore).set ↔ 0 ≤ t ∧ ∀ x, 0 ≤ x → x ≤ t →
      x ∈ ignore.set ∨ obj.at x ≠ FourValued.ii := by -- --- PROOF ---
  -- the conclusive times: in `ignore`, or not inconclusive
  obtain ⟨hvs, hset⟩ := PointSegmentSignal.set_spec obj.isInconclusive hobj.2 ignore false
  unfold FourValuedSignal.conclusiveInterval
  dsimp only
  have hCv := PointSegmentSignal.not_isValid _ hvs
  have hCat : ∀ x : ℝ, 0 ≤ x → ((obj.isInconclusive.set ignore false).not.at x = true ↔
      x ∈ ignore.set ∨ obj.at x ≠ FourValued.ii) := by
    intro x hx
    rw [PointSegmentSignal.not_at _ hvs]
    by_cases hm : x ∈ ignore.set
    · rw [(hset x hx).1 hm]; simp [hm]
    · rw [(hset x hx).2 hm]
      simp [hm, FourValuedSignal.at_eq_ii_iff]
  generalize (obj.isInconclusive.set ignore false).not = C at hCv hCat ⊢
  split_ifs with h0
  · -- inconclusive at `0`: no conclusive time
    constructor
    · intro h; exact absurd h (by simp [STLInterval.set])
    · rintro ⟨ht, hall⟩
      exact absurd ((hCat 0 le_rfl).2 (hall 0 le_rfl ht)) (by simp [h0])
  · have h0' : C.at 0 = true := by simpa using h0
    obtain ⟨hvc, -⟩ := C.cutAtFirstFallingEdge_spec hCv
    -- the cut signal is `true` exactly while `C` has been `true` from `0`
    have hP : ∀ x : ℝ, 0 ≤ x → (C.cutAtFirstFallingEdge.at x = true ↔
        ∀ y, 0 ≤ y → y ≤ x → C.at y = true) := by
      intro x hx
      rw [C.cutAtFirstFallingEdge_at hCv x hx]
      constructor
      · rintro ⟨-, hmono⟩ y hy hyx
        exact hmono 0 y le_rfl hy hyx h0'
      · intro h
        exact ⟨h x hx le_rfl, fun t₁ t₂ h1 h12 h2 hv => h t₂ (h1.trans h12) h2⟩
    have hex : ∃ x : ℝ, 0 ≤ x ∧ C.cutAtFirstFallingEdge.at x = true :=
      ⟨0, le_rfl, (hP 0 le_rfl).2 fun y hy hy0 => by rw [le_antisymm hy0 hy]; exact h0'⟩
    obtain ⟨hlub, hincl⟩ := (C.cutAtFirstFallingEdge.findLast_spec hvc true).1 hex
    -- the end of the cut signal is the end of the interval
    rw [STLInterval.mem_set_stlIntervalBounds _ _ _ _ le_rfl]
    simp only [STLInterval.IsInBounds]
    have hrhs : (0 ≤ t ∧ ∀ x : ℝ, 0 ≤ x → x ≤ t → x ∈ ignore.set ∨ obj.at x ≠ FourValued.ii) ↔
        0 ≤ t ∧ ∀ y, 0 ≤ y → y ≤ t → C.at y = true :=
      and_congr_right fun _ => forall_congr' fun x => forall_congr' fun hx =>
        forall_congr' fun _ => (hCat x hx).symm
    rw [hrhs]
    constructor
    · rintro ⟨h1, h2⟩
      have ht : 0 ≤ t := by
        rcases h1 with h | ⟨-, h⟩
        · exact h.le
        · exact h.ge
      refine ⟨ht, ?_⟩
      rcases h2 with h | ⟨hin, he⟩
      · -- below the end: some time of the cut signal is later
        obtain ⟨x, hxS, hxt⟩ : ∃ x ∈ {x : WithTop ℝ | ∃ s : ℝ, 0 ≤ s ∧
            C.cutAtFirstFallingEdge.at s = true ∧ (s : WithTop ℝ) = x}, (t : WithTop ℝ) < x := by
          by_contra hn
          push Not at hn
          exact absurd (hlub.2 fun x hx => hn x hx) (not_le.2 h)
        obtain ⟨s', hs0, hs1, rfl⟩ := hxS
        have := (hP s' hs0).1 hs1
        exact fun y hy hyt => this y hy (hyt.trans (WithTop.coe_lt_coe.1 hxt).le)
      -- at the end: the end is attained, by a time of the cut signal
      · obtain ⟨s', hs0, hs1, hse⟩ := (hincl.1 hin)
        have : s' = t := WithTop.coe_inj.1 (hse.trans he.symm)
        rw [this] at hs1
        exact (hP t ht).1 hs1
    -- the path from `0` to `t` makes `t` a time of the cut signal
    · rintro ⟨ht, hQ⟩
      have hcut : C.cutAtFirstFallingEdge.at t = true := (hP t ht).2 hQ
      have hle : (t : WithTop ℝ) ≤ (C.cutAtFirstFallingEdge.findLast true).1 :=
        hlub.1 ⟨t, ht, hcut, rfl⟩
      refine ⟨?_, ?_⟩
      · rcases ht.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr ⟨trivial, h.symm⟩
      · rcases hle.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hincl.2 ⟨t, ht, hcut, h⟩, h⟩
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
