module

public import CORALean.Global.Radstrom
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

/-!
# Adding a bounded set keeps the Hausdorff distance

`d(A + X, B + X) = d(A, B)` for convex `A`, `B` whose thickenings `A + λS` and
`B + λS` are closed, with `S` the closed unit ball and `X` bounded and nonempty.
Adding `X` to both sides of `B ⊆ A + λS` can only keep it true, which gives `≤`.
Rådström's cancellation law takes `X` back off, which gives `≥`.

Stated at `Metric.hausdorffEDist`, not at `hausdorffDist`: the source's convex
sets need not be bounded, so their distance may be infinite, and `hausdorffDist`
reads that as `0`.

The source asks `X` bounded and not nonempty. At `X = ∅` both sums are empty and
their distance is `0`, so the hypothesis is needed. It is the same unstated one
that [1, Lemma 1] uses.

## References

* [1] H. Rådström. "An embedding theorem for spaces of convex sets".
      Proc. Amer. Math. Soc. 3 (1952), pp. 165-169.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise Metric

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [NormedSpace ℝ α] in
/-- Translating both points by `x` keeps their distance, so a summand shared by
both sides can only bring the sets closer: every `a + x` has `b + x` in reach. -/
theorem aux_infEDist_add_le {a x : α} {B X : Set α} (hx : x ∈ X) :
    infEDist (a + x) (B + X) ≤ infEDist a B := by
  refine le_infEDist.2 fun b hb => ?_
  calc infEDist (a + x) (B + X)
      ≤ edist (a + x) (b + x) := infEDist_le_edist_of_mem (Set.add_mem_add hb hx)
    _ = edist a b := edist_add_right a b x

/-- Below any finite `c` above `d(B + X, A + X)`, every point of `B` is within
`c` of `A`. The sums put `B + X` inside `(A + cS) + X`, and cancelling `X` puts
`B` inside `A + cS`. -/
theorem aux_infEDist_le_of_hausdorffEDist_add_lt {A B X : Set α} (hAconv : Convex ℝ A)
    (hAcl : ∀ r : ℝ, 0 ≤ r → IsClosed (A + Metric.closedBall (0 : α) r))
    (hX : X.Nonempty) (hXb : Bornology.IsBounded X) {c : ENNReal} (hct : c ≠ ⊤)
    (hc : hausdorffEDist (B + X) (A + X) < c) : -- --- STMT ---
    ∀ b ∈ B, infEDist b A ≤ c := by -- --- PROOF ---
  set r := c.toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hcr : c = ENNReal.ofReal r := (ENNReal.ofReal_toReal hct).symm
  -- every point of `B + X` has a point of `A + X` closer than `c`, so it sits in `(A + rS) + X`
  have hsub : B + X ⊆ (A + Metric.closedBall (0 : α) r) + X := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := infEDist_lt_iff.1
      ((infEDist_le_hausdorffEDist_of_mem hp).trans_lt hc)
    obtain ⟨a, ha, x, hx, rfl⟩ := Set.mem_add.1 hq
    rw [hcr, edist_lt_ofReal] at hpq
    refine Set.mem_add.2 ⟨a + (p - (a + x)), Set.add_mem_add ha ?_, x, hx, by abel⟩
    rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    exact hpq.le
  -- cancel `X`, then read `b = a + v` with `‖v‖ ≤ r` as a distance to `A`
  have hB := radstrom_cancel hX hXb (hAconv.add (convex_closedBall 0 r)) (hAcl r hr0) hsub
  intro b hb
  obtain ⟨a, ha, v, hv, rfl⟩ := Set.mem_add.1 (hB hb)
  calc infEDist (a + v) A
      ≤ edist (a + v) a := infEDist_le_edist_of_mem ha
    _ ≤ c := by
        rw [hcr, edist_le_ofReal hr0, dist_eq_norm, add_sub_cancel_left]
        exact mem_closedBall_zero_iff.1 hv


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 3]: a bounded nonempty summand shared by two convex sets with
closed thickenings leaves their Hausdorff distance unchanged. -/
theorem hausdorffEDist_add_eq {A B X : Set α} (hAconv : Convex ℝ A) (hBconv : Convex ℝ B)
    (hAcl : ∀ r : ℝ, 0 ≤ r → IsClosed (A + Metric.closedBall (0 : α) r))
    (hBcl : ∀ r : ℝ, 0 ≤ r → IsClosed (B + Metric.closedBall (0 : α) r))
    (hX : X.Nonempty) (hXb : Bornology.IsBounded X) : -- --- STMT ---
    hausdorffEDist (A + X) (B + X) = hausdorffEDist A B := by -- --- PROOF ---
  refine le_antisymm ?_ ?_
  -- adding `X` moves each point of either sum no further than its summand was
  · refine hausdorffEDist_le_of_infEDist ?_ ?_
    · rintro _ ⟨a, ha, x, hx, rfl⟩
      exact (aux_infEDist_add_le hx).trans (infEDist_le_hausdorffEDist_of_mem ha)
    · rintro _ ⟨b, hb, x, hx, rfl⟩
      exact (aux_infEDist_add_le hx).trans
        (by rw [hausdorffEDist_comm]; exact infEDist_le_hausdorffEDist_of_mem hb)
  -- the other way, at every level above the sums' distance: cancellation, each side in turn
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    rcases eq_or_ne c ⊤ with rfl | hct
    · exact le_top
    refine hausdorffEDist_le_of_infEDist ?_ ?_
    · exact aux_infEDist_le_of_hausdorffEDist_add_lt hBconv hBcl hX hXb hct hc
    · exact aux_infEDist_le_of_hausdorffEDist_add_lt hAconv hAcl hX hXb hct
        (by rwa [hausdorffEDist_comm])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
