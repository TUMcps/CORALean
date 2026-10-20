module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# How far a zonotope's box can be from the zonotope

[1, Thm. 1]'s `ω_rad` bound, and only that one: the box over-approximation sits within the
generators' total length of the zonotope, because every point of the box is that far from the
center and the zonotope contains its center. The sharper `ω_max` and `ω_cut` are not proved here.
The distance is Mathlib's, read in the metric `Vec ℝ n` carries — the *supremum* norm. The paper
writes `‖·‖₂`, which is `norm₂` here and not this type's metric, so this is that bound at this
type's own norm (`norm_le_pi_norm`, `pi_norm_le_iff_of_nonneg`). No finiteness hypothesis is
needed: `hausdorffDist_le_of_mem_dist` bounds the distance from above, and the junk value a `⊤`
edistance would give is `0`, which any such bound already admits.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the Hausdorff distance to the box is at most the sum of generator norms

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
center's, each generator entry being at most that generator's norm. -/
theorem aux_abs_sub_center_le {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n}
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
  -- the other way the box is reached from the center, which the zonotope holds
  intro x hx
  refine ⟨Z.c, Z.center_mem_construct, ?_⟩
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hr]
  exact fun i => by rw [Real.norm_eq_abs]; exact aux_abs_sub_center_le hx i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
