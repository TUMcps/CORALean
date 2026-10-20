module

public import CORALean.Specification.FiniteSignal.Operations.Until
public import CORALean.Specification.FiniteSignal.Theorems.AtIsSome
public import CORALean.Specification.FiniteSignal.Theorems.AtSpec
public import CORALean.Specification.FiniteSignal.Theorems.CombineSpec
public import CORALean.Specification.FiniteSignal.Theorems.IndicatorSpec
public import CORALean.Specification.FiniteSignal.Theorems.MkEqSomeIff

@[expose] public section

/-!
# What `until` computes

For valid signals of the same duration `dur`, `until` returns a valid signal of that duration
which is true at `t ∈ [0, dur]` exactly if `t` is in the piece `[lo, hi)` (closed at `dur` if `hi
≥ dur`) that some pair of a run of the left signal and a run of the right signal gives: `((lint(i)
& rint(j)) - int) & lint(i)`, if that is not empty and has positive volume. The runs are the
closed cells where the signal is true (`findIntervals_spec`), so a piece reaches the breakpoint
that closes a run, and `&` has the tolerance `eps` of `and_`.

## Inputs
* `eps` – machine epsilon
* `lsig` – left signal
* `rsig` – right signal
* `p` – interval lower bound
* `q` – interval upper bound

## Hypotheses
* `hl` – the left signal is valid
* `hd` – both signals have equal duration

## Conclusion
* a valid signal true exactly on the pieces of matching interval pairs
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop of `until`: every pair of runs adds the times of its piece to the true times. -/
theorem aux_until_fold (eps p : ℝ) (q : EReal) (dur : ℝ) (h0 : 0 ≤ dur) :
    ∀ (prs : List ((ℝ × ℝ) × (ℝ × ℝ))) (sig : FiniteSignal ℝ Bool), sig.IsValid →
      sig.duration = dur → ∃ r, prs.foldlM (FiniteSignal.aux_untilStep eps p q dur) sig = some r ∧
        r.IsValid ∧ r.duration = dur ∧ ∀ t : ℝ, 0 ≤ t → t ≤ dur → ∃ v, r.at? t = some v ∧
          (v = true ↔ (sig.at? t = some true ∨ ∃ LR ∈ prs, ∃ lo hi,
            FiniteSignal.aux_untilPiece eps p q LR.1 LR.2 = some (lo, hi) ∧ lo < hi ∧
              (0 < hi ∧ lo < dur ∧ lo ≤ t ∧ (t < hi ∨ dur ≤ hi))))
  | [], sig, hs, hd => by
    refine ⟨sig, rfl, hs, hd, fun t ht0 ht1 => ?_⟩
    obtain ⟨v, hv⟩ := FiniteSignal.at?_isSome sig hs t ht0 (hd ▸ ht1)
    exact ⟨v, hv, by simp [hv]⟩
  | LR :: rest, sig, hs, hd => by
    -- pairs of runs after `LR`, with the signal after it
    have hrest : ∀ sig' : FiniteSignal ℝ Bool, sig'.IsValid → sig'.duration = dur →
        FiniteSignal.aux_untilStep eps p q dur sig LR = some sig' →
        ∃ r, (LR :: rest).foldlM (FiniteSignal.aux_untilStep eps p q dur) sig = some r ∧ r.IsValid ∧
          r.duration = dur ∧ ∀ t : ℝ, 0 ≤ t → t ≤ dur → ∃ v, r.at? t = some v ∧
            (v = true ↔ (sig'.at? t = some true ∨ ∃ LR' ∈ rest, ∃ lo hi,
              FiniteSignal.aux_untilPiece eps p q LR'.1 LR'.2 = some (lo, hi) ∧ lo < hi ∧
                (0 < hi ∧ lo < dur ∧ lo ≤ t ∧ (t < hi ∨ dur ≤ hi)))) := fun sig' hv hdd hstep => by
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ := aux_until_fold eps p q dur h0 rest sig' hv hdd
      refine ⟨r, ?_, hr2, hr3, hr4⟩
      rw [List.foldlM_cons, hstep]
      exact hr1
    -- the case of the piece of `LR`
    rcases hpc : FiniteSignal.aux_untilPiece eps p q LR.1 LR.2 with _ | ⟨lo, hi⟩
    · -- empty: the signal stays
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hrest sig hs hd (by simp [FiniteSignal.aux_untilStep, hpc])
      refine ⟨r, hr1, hr2, hr3, fun t ht0 ht1 => ?_⟩
      obtain ⟨v, hv, hvi⟩ := hr4 t ht0 ht1
      refine ⟨v, hv, hvi.trans ?_⟩
      simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, hpc]
      simp
    · by_cases hlh : lo < hi
      · -- a piece of positive length: or-ed with its indicator
        obtain ⟨ind, hind1, hind2, hind3, hind4⟩ :=
          FiniteSignal.indicator?_spec dur lo hi true h0 (EReal.coe_lt_coe_iff.mpr hlh)
        obtain ⟨sig', hc1, hc2, hc3, hc4⟩ :=
          FiniteSignal.combine?_spec (fun x y => x || y) sig ind hs hind2
        -- the fact `hdd`
        have hdd : sig'.duration = dur := by rw [hc3, hd, hind3, min_self]
        obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hrest sig' hc2 hdd (by
          simp [FiniteSignal.aux_untilStep, hpc, hlh, hind1, hc1])
        refine ⟨r, hr1, hr2, hr3, fun t ht0 ht1 => ?_⟩
        obtain ⟨v, hv, hvi⟩ := hr4 t ht0 ht1
        refine ⟨v, hv, ?_⟩
        -- the value of `sig'` at `t`
        obtain ⟨x, hx⟩ := FiniteSignal.at?_isSome sig hs t ht0 (hd ▸ ht1)
        have hy := hind4 t ht0 ht1
        have hok : t < sig.duration ∧ t < ind.duration ∨
            sig.duration = ind.duration ∧ t = sig.duration := by
          rcases ht1.lt_or_eq with h | h
          · exact Or.inl ⟨hd ▸ h, hind3 ▸ h⟩
          · exact Or.inr ⟨hd.trans hind3.symm, hd ▸ h⟩
        have hs' := hc4 t x _ hx hy hok
        rw [hs'] at hvi
        rw [hvi]
        simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, hpc]
        simp only [Option.some.injEq, Bool.or_eq_true, hx, decide_eq_true_eq]
        simp [hlh, or_assoc]
      · -- a piece without length: the signal stays
        -- unpack the facts from the previous steps
        obtain ⟨r, hr1, hr2, hr3, hr4⟩ :=
          hrest sig hs hd (by simp [FiniteSignal.aux_untilStep, hpc, hlh])
        refine ⟨r, hr1, hr2, hr3, fun t ht0 ht1 => ?_⟩
        obtain ⟨v, hv, hvi⟩ := hr4 t ht0 ht1
        refine ⟨v, hv, hvi.trans ?_⟩
        simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, hpc]
        simp [hlh]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.until?_spec (eps : ℝ) (lsig rsig : FiniteSignal ℝ Bool) (p : ℝ) (q : EReal)
    (hl : lsig.IsValid) (hd : lsig.duration = rsig.duration) : -- --- CONCL ---
    ∃ r, FiniteSignal.until? eps lsig p q rsig = some r ∧ r.IsValid ∧
      r.duration = lsig.duration ∧ ∀ t : ℝ, 0 ≤ t → t ≤ lsig.duration →
        (r.at? t = some true ↔ ∃ L ∈ lsig.findIntervals (fun v => decide (true ≤ v)),
          ∃ R ∈ rsig.findIntervals (fun v => decide (true ≤ v)), ∃ lo hi,
            FiniteSignal.aux_untilPiece eps p q L R = some (lo, hi) ∧ lo < hi ∧
              (0 < hi ∧ lo < lsig.duration ∧ lo ≤ t ∧
                (t < hi ∨ lsig.duration ≤ hi))) := by -- --- PROOF ---
  -- the duration is nonnegative, and the signals have the same one
  obtain ⟨hmem, -⟩ := FiniteSignal.time_le_duration lsig hl
  have h0 : 0 ≤ lsig.duration := hl.2.2.2.2 _ hmem
  unfold FiniteSignal.until?
  rw [if_neg (not_not.mpr hd)]
  -- the signal starts as the constant false signal
  have hv0 : (⟨[lsig.duration], [false]⟩ : FiniteSignal ℝ Bool).IsValid :=
    ⟨by simp, by simp, by simp, by simp, fun t ht => by simp at ht; rw [ht]; exact h0⟩
  have hmk := (FiniteSignal.mk?_eq_some_iff [lsig.duration] [false]
    (⟨[lsig.duration], [false]⟩ : FiniteSignal ℝ Bool)).mpr ⟨rfl, rfl, hv0⟩
  rw [hmk]
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := aux_until_fold eps p q lsig.duration h0
    ((lsig.findIntervals (fun v => decide (true ≤ v))).flatMap fun L =>
      (rsig.findIntervals (fun v => decide (true ≤ v))).map fun R => (L, R))
    ⟨[lsig.duration], [false]⟩ hv0 (by simp [FiniteSignal.duration])
  refine ⟨r, hr1, hr2, hr3, fun t ht0 ht1 => ?_⟩
  obtain ⟨v, hv, hvi⟩ := hr4 t ht0 ht1
  rw [hv, Option.some.injEq, hvi]
  -- the constant false signal is false at `t`
  have hf : (⟨[lsig.duration], [false]⟩ : FiniteSignal ℝ Bool).at? t ≠ some true := by
    rw [FiniteSignal.at?_eq_valueAt _ hv0.2.1 t,
      if_pos ⟨ht0, by simpa [FiniteSignal.duration] using ht1⟩]
    simp [FiniteSignal.pairs, FiniteSignal.valueAt]
  simp only [hf, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨LR, ⟨L, hL, R, hR, rfl⟩, h⟩
    exact ⟨L, hL, R, hR, h⟩
  · rintro ⟨L, hL, R, hR, h⟩
    exact ⟨(L, R), ⟨L, hL, R, hR, rfl⟩, h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
