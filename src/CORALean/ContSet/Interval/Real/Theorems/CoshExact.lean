module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# `Interval.cosh` is exactly the image under `Real.cosh`

The hyperbolic cosine is continuous and even, decreasing on `(-∞, 0]` and increasing on `[0, ∞)`.
On one coordinate `[a, b]` the image is the interval from `coshLo` to `coshHi`, by the intermediate
value theorem on the monotone piece that carries the target value. A crossed coordinate
(`b < a`) would give a nonempty box for an empty one, so the statement is for a nonempty box.

[1, Eq. 7], all three cases.

## Inputs
* `I` – interval box

## Hypotheses
* `hI` – `I` has ordered bounds

## Conclusion
* the hyperbolic cosine box is exactly the image of `I`

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Interval.aux_cosh_mono {x y : ℝ} (h0 : 0 ≤ x) (h : x ≤ y) :
    Real.cosh x ≤ Real.cosh y := by
  rw [Real.cosh_le_cosh, abs_of_nonneg h0, abs_of_nonneg (h0.trans h)]; exact h

theorem Interval.aux_cosh_anti {x y : ℝ} (h : y ≤ x) (h0 : x ≤ 0) :
    Real.cosh x ≤ Real.cosh y := by
  rw [Real.cosh_le_cosh, abs_of_nonpos h0, abs_of_nonpos (h.trans h0)]; linarith

/-- One coordinate: the image of `[a, b]` is `[coshLo a b, coshHi a b]`. -/
theorem Interval.aux_cosh_Icc {a b : ℝ} (hab : a ≤ b) : -- --- CONCL ---
    Set.Icc (Interval.coshLo a b) (Interval.coshHi a b) =
      Real.cosh '' Set.Icc a b := by -- --- PROOF ---
  have hc : ∀ c d : ℝ, ContinuousOn Real.cosh (Set.Icc c d) := fun _ _ =>
    Real.continuous_cosh.continuousOn
  unfold Interval.coshLo Interval.coshHi
  -- the box left of `0`: `cosh` decreases, the image is `[cosh b, cosh a]`
  by_cases h1 : b ≤ 0
  · simp only [h1, if_true]
    refine Set.Subset.antisymm (intermediate_value_Icc' hab (hc a b)) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Interval.aux_cosh_anti hx.2 h1, Interval.aux_cosh_anti hx.1 (hx.2.trans h1)⟩
  · -- right of `0`: `cosh` increases
    by_cases h2 : 0 ≤ a
    · simp only [h1, h2, if_false, if_true]
      refine Set.Subset.antisymm (intermediate_value_Icc hab (hc a b)) ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨Interval.aux_cosh_mono h2 hx.1, Interval.aux_cosh_mono (h2.trans hx.1) hx.2⟩
    · -- `0` inside: the minimum is `1`, the maximum at the end of larger absolute value
      simp only [h1, h2, if_false]
      have ha : a < 0 := not_le.1 h2
      have hb : 0 < b := not_le.1 h1
      refine Set.Subset.antisymm ?_ ?_
      · -- a target value is reached on the monotone piece that holds the larger end
        intro y hy
        rcases le_total |a| |b| with h | h
        · rw [max_eq_right h, abs_of_pos hb] at hy
          have := intermediate_value_Icc hb.le (hc 0 b) (by simpa using hy)
          obtain ⟨x, hx, hxy⟩ := this
          exact ⟨x, ⟨by linarith [hx.1], hx.2⟩, hxy⟩
        · rw [max_eq_left h, abs_of_neg ha, Real.cosh_neg] at hy
          have := intermediate_value_Icc' ha.le (hc a 0)
            (show y ∈ Set.Icc (Real.cosh 0) (Real.cosh a) by simpa using hy)
          obtain ⟨x, hx, hxy⟩ := this
          exact ⟨x, ⟨hx.1, by linarith [hx.2]⟩, hxy⟩
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨Real.one_le_cosh x, ?_⟩
        rw [Real.cosh_le_cosh, abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
        exact abs_le_max_abs_abs hx.1 hx.2


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.cosh_exact (I : Interval (Vec ℝ n))
    (hI : ∀ i, I.inf i ≤ I.sup i) : -- --- CONCL ---
    I.cosh.construct = (fun x i => Real.cosh (x i)) '' I.construct := by -- --- PROOF ---
  ext y
  constructor
  · intro hy
    have hex : ∀ i, ∃ x, x ∈ Set.Icc (I.inf i) (I.sup i) ∧ Real.cosh x = y i := fun i => by
      have h := (Interval.aux_cosh_Icc (hI i)).subset (hy i)
      exact h
    choose x hx hfx using hex
    exact ⟨x, fun i => hx i, funext hfx⟩
  · rintro ⟨x, hx, rfl⟩ i
    exact (Interval.aux_cosh_Icc (hI i)).superset ⟨x i, hx i, rfl⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
