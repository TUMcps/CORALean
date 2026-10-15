module

public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Operations.Until
public import CORALean.Specification.KleeneSignal.Theorems.MinMaxSpec
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalAtIff
public import CORALean.Specification.PointSegmentSignal.Theorems.UntilSpec
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet

@[expose] public section

/-!
# The until of three-valued signals

For valid signals over `ℝ` and an until interval with lower bound `≥ 0`, `until(lhs,interval,rhs)`
is valid. At a time `t ≥ 0` it is `True` iff some `t'` with `t' - t` in the interval has the
right-hand side `True` and the left-hand side `True` strictly between, and `False` iff at every such
`t'` the right-hand side is `False` or the left-hand side is `False` somewhere strictly between.

This is the direct semantics of `U_I` in [1, Eq. 2], the unknown case being the remaining one.

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

/-- The until of Kleene signals is `True` and `False` as Kleene's quantified connectives say. -/
theorem KleeneSignal.until_spec (lhs rhs : KleeneSignal ℝ) (hl : lhs.IsValid) (hr : rhs.IsValid)
    (U : STLInterval) (hU : ∀ f, U.fieldsOf = some f → 0 ≤ f.lower) :
    (lhs.until U rhs).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((lhs.until U rhs).at t = Kleene.tt ↔ ∃ t', t' - t ∈ U.set ∧ rhs.at t' = Kleene.tt ∧
        ∀ x, t < x → x < t' → lhs.at x = Kleene.tt) ∧
      ((lhs.until U rhs).at t = Kleene.ff ↔ ∀ t', t' - t ∈ U.set →
        rhs.at t' = Kleene.ff ∨ ∃ x, t < x ∧ x < t' ∧ lhs.at x = Kleene.ff) := by -- --- PROOF ---
  -- the refinements are valid, and so are their untils
  have hlf := (KleeneSignal.toBoolSignal_spec lhs hl false).1
  have hrf := (KleeneSignal.toBoolSignal_spec rhs hr false).1
  have hlt := (KleeneSignal.toBoolSignal_spec lhs hl true).1
  have hrt := (KleeneSignal.toBoolSignal_spec rhs hr true).1
  obtain ⟨hvm, hm⟩ := PointSegmentSignal.until_spec _ _ hlf hrf U hU
  obtain ⟨hvx, hx⟩ := PointSegmentSignal.until_spec _ _ hlt hrt U hU
  obtain ⟨hv, h⟩ := KleeneSignal.minMax_spec _ _ hvm hvx
  refine ⟨hv, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht
  simp only [Bool.eq_false_iff, ne_eq] at h2
  rw [hm t ht, hx t ht] at h1 h2
  -- a witness `t'` lies after `t`, so the refinements are read there by `toBoolSignal_at_iff`
  have hpos : ∀ t', t' - t ∈ U.set → 0 ≤ t' := fun t' hu => by
    have := STLInterval.zero_le_of_mem_set U hU _ hu; linarith
  have hM : (∃ t', t' - t ∈ U.set ∧ (rhs.toBoolSignal false).at t' = true ∧
      ∀ x, t < x → x < t' → (lhs.toBoolSignal false).at x = true) ↔
      ∃ t', t' - t ∈ U.set ∧ rhs.at t' = Kleene.tt ∧
        ∀ x, t < x → x < t' → lhs.at x = Kleene.tt := by
    refine exists_congr fun t' => and_congr_right fun hu => and_congr ?_ ?_
    · exact (KleeneSignal.toBoolSignal_at_iff rhs hr t' (hpos t' hu)).1
    · exact forall_congr' fun x => forall_congr' fun hx1 => forall_congr' fun hx2 =>
        (KleeneSignal.toBoolSignal_at_iff lhs hl x (by linarith)).1
  have hX : (∃ t', t' - t ∈ U.set ∧ (rhs.toBoolSignal true).at t' = true ∧
      ∀ x, t < x → x < t' → (lhs.toBoolSignal true).at x = true) ↔
      ∃ t', t' - t ∈ U.set ∧ rhs.at t' ≠ Kleene.ff ∧
        ∀ x, t < x → x < t' → lhs.at x ≠ Kleene.ff := by
    refine exists_congr fun t' => and_congr_right fun hu => and_congr ?_ ?_
    · exact (KleeneSignal.toBoolSignal_at_iff rhs hr t' (hpos t' hu)).2
    · exact forall_congr' fun x => forall_congr' fun hx1 => forall_congr' fun hx2 =>
        (KleeneSignal.toBoolSignal_at_iff lhs hl x (by linarith)).2
  rw [hM, hX] at h1 h2
  -- `True` of the minimal refinement gives not `False` of the maximal one
  have hMX : (∃ t', t' - t ∈ U.set ∧ rhs.at t' = Kleene.tt ∧
      ∀ x, t < x → x < t' → lhs.at x = Kleene.tt) → ∃ t', t' - t ∈ U.set ∧ rhs.at t' ≠ Kleene.ff ∧
      ∀ x, t < x → x < t' → lhs.at x ≠ Kleene.ff := by
    rintro ⟨t', hu, hr', hl'⟩
    exact ⟨t', hu, by simp [hr'], fun x a b => by simp [hl' x a b]⟩
  constructor
  · exact h1.trans ⟨fun h => h.1, fun h => ⟨h, hMX h⟩⟩
  -- `False`: the maximal refinement is `False`, and so is the minimal one
  · refine h2.trans ?_
    constructor
    · rintro ⟨-, hn⟩ t' hu
      by_contra hneg
      push Not at hneg
      exact hn ⟨t', hu, hneg.1, fun x a b => by
        have := hneg.2 x a b
        exact this⟩
    · intro H
      have hnX : ¬ ∃ t', t' - t ∈ U.set ∧ rhs.at t' ≠ Kleene.ff ∧
          ∀ x, t < x → x < t' → lhs.at x ≠ Kleene.ff := by
        rintro ⟨t', hu, h1, h2⟩
        rcases H t' hu with h | ⟨x, a, b, hx⟩
        · exact h1 h
        · exact h2 x a b hx
      exact ⟨fun hM' => hnX (hMX hM'), hnX⟩
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
