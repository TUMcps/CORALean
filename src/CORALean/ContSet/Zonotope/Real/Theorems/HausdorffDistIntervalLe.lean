module

public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# How far a zonotope's box can be from the zonotope

[1, Thm. 1]'s `ω_rad` bound, and only that one: the box over-approximation sits
within the generators' total length of the zonotope, because every point of the
box is that far from the centre and the zonotope contains its centre. The
paper's two sharper bounds, `ω_max` and `ω_cut`, are not proved here.

The distance is Mathlib's, so it is read in the metric `Vec ℝ n` carries — the
*supremum* norm, `Vec ℝ n` being `Fin n → ℝ`. The paper writes `‖·‖₂`
throughout, which is `norm₂` here and is not this type's metric, so this is
that bound at this type's own norm rather than at the Euclidean one. The
steps naming a norm are `norm_le_pi_norm` and `pi_norm_le_iff_of_nonneg`.

No finiteness hypothesis is needed: `hausdorffDist_le_of_mem_dist` bounds the
distance from above, and the junk value a `⊤` edistance would give is `0`,
which any such bound already admits. Both sets are compact and nonempty here
regardless, so what is bounded is the distance and not the junk.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability
      Algorithms for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear
      Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A coordinate of the box is within the generators' total length of the
centre's, each generator entry being at most that generator's norm. -/
theorem aux_abs_sub_centre_le {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n}
    (hx : x ∈ Z.interval.construct) (i : Fin n) :
    |x i - Z.c i| ≤ ∑ p, ‖Z.G p‖ := by -- --- PROOF ---
  have hb := hx i
  simp only [Zonotope.interval, entry_ofEntry] at hb
  have hle : ∑ j, |entry (Z.G j) i| ≤ ∑ p, ‖Z.G p‖ :=
    Finset.sum_le_sum fun j _ => by
      rw [entry_vec, ← Real.norm_eq_abs]; exact norm_le_pi_norm (Z.G j) i
  -- `entry` at a vector is an application, so the goal is already this statement
  show |entry x i - entry Z.c i| ≤ ∑ p, ‖Z.G p‖
  rw [abs_le]
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], the `ω_rad` bound: the box is never further from the zonotope
than the generators reach, measured in the norm `Vec ℝ n` carries. -/
theorem Zonotope.hausdorffDist_interval_le (Z : Zonotope (Vec ℝ n)) :
    Metric.hausdorffDist Z.construct Z.interval.construct ≤ ∑ p, ‖Z.G p‖ := by -- --- PROOF ---
  have hr : (0 : ℝ) ≤ ∑ p, ‖Z.G p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine Metric.hausdorffDist_le_of_mem_dist hr
    (fun x hx => ⟨x, Z.interval_contains hx, by simpa using hr⟩) ?_
  -- the other way the box is reached from the centre, which the zonotope holds
  intro x hx
  refine ⟨Z.c, Z.centre_mem_construct, ?_⟩
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hr]
  exact fun i => by rw [Real.norm_eq_abs]; exact aux_abs_sub_centre_le hx i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
