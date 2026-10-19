module

public import CORALean.Global.CoordinatePath
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# A coordinate move with a partial bounded away from zero gains at least its bound

[1, Thm. 3] (via [1, Thm. 2]) needs the *corner* of a box, not just some point of it: when
`|∂ⱼf| ≥ d` on the whole box, `∂ⱼf` keeps one sign there (a continuous function that does
not vanish on a connected set), so moving coordinate `j` from the center to one end of its
interval raises `f` by at least `d rⱼ` from wherever the other coordinates are, and moving
to the other end lowers it by as much. The end does not depend on the other coordinates,
which is what makes the parametrization of `Thm. 3`'s fixed-point argument continuous.
`d ≤ 0` asks nothing, and the center is both ends.

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to
      Reachability of Non-Linear Control Systems With Disturbances". IEEE Control Systems
      Letters, 4(4):928-933, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `|∂ⱼf| ≥ d` on the box, the ends `b` and `a` of coordinate `j` raise and lower `f`
from the center of that coordinate by at least `d rⱼ`, for every position of the others. -/
theorem exists_coord_ends_gain {f : (Fin m → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {lo hi : Fin m → ℝ}
    (hlh : lo ≤ hi) (j : Fin m) (d : ℝ)
    (hd : ∀ y ∈ Icc lo hi, d ≤ |fderiv ℝ f y (Pi.single j 1)|) : -- --- CONCL ---
    ∃ a ∈ Icc (lo j) (hi j), ∃ b ∈ Icc (lo j) (hi j),
      (∀ p ∈ Icc lo hi, f (Function.update p j ((lo j + hi j) / 2)) + d * ((hi j - lo j) / 2)
        ≤ f (Function.update p j b)) ∧
      (∀ p ∈ Icc lo hi, f (Function.update p j a) + d * ((hi j - lo j) / 2)
        ≤ f (Function.update p j ((lo j + hi j) / 2))) := by -- --- PROOF ---
  have hcj : (lo j + hi j) / 2 ∈ Icc (lo j) (hi j) :=
    ⟨by linarith [hlh j], by linarith [hlh j]⟩
  have hr : 0 ≤ (hi j - lo j) / 2 := by linarith [hlh j]
  by_cases hd0 : d ≤ 0
  · refine ⟨_, hcj, _, hcj, fun p _ => ?_, fun p _ => ?_⟩ <;>
      nlinarith [mul_nonneg (neg_nonneg.mpr hd0) hr]
  push Not at hd0
  set g : (Fin m → ℝ) → ℝ := fun y => fderiv ℝ f y (Pi.single j 1) with hg
  have hgc : Continuous g := (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hconn : IsPreconnected (Icc lo hi) := (convex_Icc lo hi).isPreconnected
  have habs : ∀ y ∈ Icc lo hi, d ≤ g y ∨ g y ≤ -d := fun y hy => by
    rcases le_abs'.mp (hd y hy) with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- the sign of `∂ⱼf` is the same all over the box
  have hsign : (∀ y ∈ Icc lo hi, d ≤ g y) ∨ (∀ y ∈ Icc lo hi, g y ≤ -d) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨y1, hy1, h1⟩, ⟨y2, hy2, h2⟩⟩ := hcon
    have h1' : g y1 ≤ -d := (habs y1 hy1).resolve_left (not_le.mpr h1)
    have h2' : d ≤ g y2 := (habs y2 hy2).resolve_right (not_le.mpr h2)
    obtain ⟨y, hy, hy0⟩ := hconn.intermediate_value hy1 hy2 hgc.continuousOn
      (show (0 : ℝ) ∈ Icc (g y1) (g y2) from ⟨by linarith, by linarith⟩)
    rcases habs y hy with h | h <;> linarith
  -- along the line of `p`
  have hline : ∀ p ∈ Icc lo hi, ∀ t ∈ Icc (lo j) (hi j),
      HasDerivAt (fun s => f (Function.update p j s)) (g (Function.update p j t)) t :=
    fun p _ t _ => hasDerivAt_comp_update (hf.differentiable one_ne_zero) p j t
  have hcont : ∀ p, ContinuousOn (fun s => f (Function.update p j s)) (Icc (lo j) (hi j)) :=
    fun p => (hf.continuous.comp (continuous_const.update j continuous_id)).continuousOn
  have hderiv : ∀ p ∈ Icc lo hi, ∀ t ∈ interior (Icc (lo j) (hi j)),
      deriv (fun s => f (Function.update p j s)) t = g (Function.update p j t) := by
    intro p hp t ht
    rw [interior_Icc] at ht
    exact (hline p hp t (Ioo_subset_Icc_self ht)).deriv
  -- the hypotheses of the one-dimensional mean-value inequalities
  have hdiff : ∀ p ∈ Icc lo hi, DifferentiableOn ℝ (fun s => f (Function.update p j s))
      (interior (Icc (lo j) (hi j))) := fun p hp t ht =>
    ((hline p hp t (interior_subset ht)).differentiableAt).differentiableWithinAt
  have hmemI : ∀ p ∈ Icc lo hi, ∀ t ∈ interior (Icc (lo j) (hi j)),
      Function.update p j t ∈ Icc lo hi := fun p hp t ht =>
    update_mem_Icc hp j (interior_subset ht)
  -- the sign is positive: the upper end raises `f`, the lower end lowers it
  rcases hsign with hpos | hneg
  · refine ⟨lo j, ⟨le_rfl, hlh j⟩, hi j, ⟨hlh j, le_rfl⟩, fun p hp => ?_, fun p hp => ?_⟩
    · have := (convex_Icc (lo j) (hi j)).mul_sub_le_image_sub_of_le_deriv (hcont p) (hdiff p hp)
        (C := d) (fun t ht => by rw [hderiv p hp t ht]; exact hpos _ (hmemI p hp t ht))
        _ hcj _ ⟨hlh j, le_rfl⟩ (by linarith [hlh j])
      nlinarith
    · have := (convex_Icc (lo j) (hi j)).mul_sub_le_image_sub_of_le_deriv (hcont p) (hdiff p hp)
        (C := d) (fun t ht => by rw [hderiv p hp t ht]; exact hpos _ (hmemI p hp t ht))
        _ ⟨le_rfl, hlh j⟩ _ hcj (by linarith [hlh j])
      nlinarith
  -- the sign is negative: the ends swap
  · refine ⟨hi j, ⟨hlh j, le_rfl⟩, lo j, ⟨le_rfl, hlh j⟩, fun p hp => ?_, fun p hp => ?_⟩
    · have := (convex_Icc (lo j) (hi j)).image_sub_le_mul_sub_of_deriv_le (hcont p) (hdiff p hp)
        (C := -d) (fun t ht => by rw [hderiv p hp t ht]; exact hneg _ (hmemI p hp t ht))
        _ ⟨le_rfl, hlh j⟩ _ hcj (by linarith [hlh j])
      nlinarith
    · have := (convex_Icc (lo j) (hi j)).image_sub_le_mul_sub_of_deriv_le (hcont p) (hdiff p hp)
        (C := -d) (fun t ht => by rw [hderiv p hp t ht]; exact hneg _ (hmemI p hp t ht))
        _ hcj _ ⟨hlh j, le_rfl⟩ (by linarith [hlh j])
      nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
