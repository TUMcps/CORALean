import CORALean.ContSet.Capsule.Real.Capsule
import CORALean.ContSet.Interval.Real.Interval

/-!
# A box as a capsule

CORA's `capsule(interval)`: the centre, the segment along the widest edge of
the box, and the thickness the ball must have to cover the rest of the box,
which is the Euclidean norm of the other half-widths. An enclosure, not an
equality: a box is a capsule only in the degenerate cases (at most one
non-degenerate edge, which is the whole box when `n ≤ 1`), and in general the
ball round the remaining edges is a ball, not a box.

`Interval.capsuleAlong I k` fixes the axis `k` of the segment, and the enclosure
holds for every `k`; `Interval.capsule` picks a widest axis as CORA does, by a computable `argmax`.
For `n = 0` there is no axis, the capsule is the point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- The capsule with the segment along axis `k` and the ball covering the other half-widths. -/
noncomputable def Interval.capsuleAlong (I : Interval (Vec ℝ n)) (k : Fin n) : Capsule n where
  c := fun i => (I.inf i + I.sup i) / 2
  g := fun i => if i = k then (I.sup i - I.inf i) / 2 else 0
  r := Real.sqrt (∑ i, if i = k then 0 else ((I.sup i - I.inf i) / 2) ^ 2)

/-- CORA's `capsule(interval)`: the segment runs along a widest edge, the first one of maximal
width. The choice is a computable `List.argmax` over the axes; only the real arithmetic is
noncomputable. For `n = 0` there is no axis and the capsule is the point. -/
noncomputable def Interval.capsule (I : Interval (Vec ℝ n)) : Capsule n :=
  match (List.finRange n).argmax (fun i => I.sup i - I.inf i) with
  | some k => I.capsuleAlong k
  | none => ⟨0, 0, 0⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.capsuleAlong_contains (I : Interval (Vec ℝ n)) (k : Fin n) :
    I.construct ⊆ (I.capsuleAlong k).construct := by -- --- PROOF ---
  intro x hx
  -- every coordinate lies within its half-width of the centre
  have hlo : ∀ i, I.inf i ≤ x i := fun i => (hx i).1
  have hhi : ∀ i, x i ≤ I.sup i := fun i => (hx i).2
  have hk : |x k - (I.inf k + I.sup k) / 2| ≤ (I.sup k - I.inf k) / 2 :=
    abs_le.mpr ⟨by linarith [hlo k, hhi k], by linarith [hlo k, hhi k]⟩
  -- a degenerate axis-k edge needs no segment (t = 0); otherwise t is the scaled offset
  by_cases h0 : (I.sup k - I.inf k) / 2 = 0
  · refine ⟨0, by simp, ?_⟩
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    by_cases hi : i = k
    · subst hi
      have : x i - (I.inf i + I.sup i) / 2 = 0 := by
        rw [h0, abs_le] at hk; linarith [hk.1, hk.2]
      simp [Interval.capsuleAlong, this]
    · simp only [Interval.capsuleAlong, hi, if_false, mul_zero, add_zero]
      have h1 : |x i - (I.inf i + I.sup i) / 2| ≤ (I.sup i - I.inf i) / 2 :=
        abs_le.mpr ⟨by linarith [hlo i, hhi i], by linarith [hlo i, hhi i]⟩
      exact sq_le_sq' (by linarith [(abs_le.mp h1).1]) (by linarith [(abs_le.mp h1).2])
  · set t : ℝ := (x k - (I.inf k + I.sup k) / 2) / ((I.sup k - I.inf k) / 2) with ht
    have hpos : 0 < (I.sup k - I.inf k) / 2 := lt_of_le_of_ne
      (le_trans (abs_nonneg _) hk) (Ne.symm h0)
    have htle : t ∈ Set.Icc (-1 : ℝ) 1 := by
      have : |t| ≤ 1 := by
        rw [ht, abs_div, abs_of_pos hpos, div_le_one hpos]; exact hk
      exact abs_le.mp this
    -- the sum of squares is the one over the other axes, bounded term by term
    refine ⟨t, htle, Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)⟩
    by_cases hi : i = k
    · subst hi
      have : x i - ((I.inf i + I.sup i) / 2 + t * ((I.sup i - I.inf i) / 2)) = 0 := by
        rw [ht, mul_comm, mul_div_cancel₀ _ h0]; ring
      simp [Interval.capsuleAlong, this]
    · simp only [Interval.capsuleAlong, hi, if_false, mul_zero, add_zero]
      exact sq_le_sq' (by linarith [hlo i, hhi i]) (by linarith [hlo i, hhi i])

theorem Interval.capsule_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.capsule.construct := by -- --- PROOF ---
  unfold Interval.capsule
  cases h : (List.finRange n).argmax (fun i => I.sup i - I.inf i) with
  | some k => exact I.capsuleAlong_contains k
  | none =>
    have hn : List.finRange n = [] := List.argmax_eq_none.mp h
    obtain rfl : n = 0 := by simpa [List.finRange_eq_nil_iff] using hn
    intro x _
    exact ⟨0, by simp, by simp⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
