module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.Global.EuclideanHausdorffDist
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# How far a zonotope's box can be from the zonotope, at the Euclidean norm

[1, Thm. 1]'s `ω_rad` bound as the paper states it, at `‖·‖₂`; `ω_max` and `ω_cut` are
`HausdorffDist2IntervalLeMax` and `HausdorffDist2IntervalLeCut`. `hausdorffDist₂` is Mathlib's
distance taken through `toEuclidean`, so this is not `Zonotope.hausdorffDist_interval_le`, the
same argument at the supremum norm `Vec ℝ n` carries: `∑ₚ ‖g⁽ᵖ⁾‖_∞` is not `∑ₚ ‖g⁽ᵖ⁾‖₂` and
neither bound implies the other. A point of the box is within the columnwise sum of generator
magnitudes of the center, which `norm₂_sum_le` prices. No finiteness hypothesis is needed:
`hausdorffDist₂_le_of_mem_dist` bounds the distance from above, and the junk value a `⊤` edistance
would give is `0`, which any such bound already admits.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the Hausdorff distance to the box is at most the sum of generator norms

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Opus 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Squaring is monotone on magnitudes, so a coordinatewise bound on magnitudes
is a bound on the Euclidean norm. -/
private theorem aux_norm₂_le_of_abs_le {x y : Vec ℝ n} (h : ∀ i, |x i| ≤ |y i|) : ‖x‖₂ ≤ ‖y‖₂ := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have hi := mul_self_le_mul_self (abs_nonneg (x i)) (h i)
  rwa [abs_mul_abs_self, abs_mul_abs_self, ← pow_two, ← pow_two] at hi

/-- A point of the box is within the generators' total length of the center:
coordinatewise it is within their columnwise magnitude sum, and that vector is
no longer than the generators are. -/
private theorem aux_norm₂_sub_center_le {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n}
    (hx : x ∈ Z.interval.construct) : -- --- CONCL ---
    ‖x - Z.c‖₂ ≤ ∑ p, ‖Z.G p‖₂ := by -- --- PROOF ---
  -- one vector per generator, read entrywise in magnitude
  let A : Fin Z.h → Vec ℝ n := fun j i => |Z.G j i|
  have hA : ∀ i, (∑ j, A j) i = ∑ j, |Z.G j i| := fun i => Finset.sum_apply i Finset.univ A
  have hbox : ∀ i, |(x - Z.c) i| ≤ |(∑ j, A j) i| := fun i => by
    have hb := hx i
    simp only [Zonotope.interval, entry_ofEntry] at hb
    have hnn : (0 : ℝ) ≤ ∑ j, |Z.G j i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [hA i, abs_of_nonneg hnn]
    -- `entry` at a vector is an application, so the goal is already this statement
    show |entry x i - entry Z.c i| ≤ ∑ j, |entry (Z.G j) i|
    rw [abs_le]
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  -- magnitudes leave a generator's own length alone, so the last step is an equality
  calc ‖x - Z.c‖₂ ≤ ‖∑ j, A j‖₂ := aux_norm₂_le_of_abs_le hbox
    _ ≤ ∑ j, ‖A j‖₂ := norm₂_sum_le _ _
    _ ≤ ∑ p, ‖Z.G p‖₂ :=
        Finset.sum_le_sum fun j _ => aux_norm₂_le_of_abs_le fun i => le_of_eq (abs_abs _)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], the `ω_rad` bound: the box is never further from the zonotope
than the generators reach, measured in the `‖·‖₂` the paper writes. -/
theorem Zonotope.hausdorffDist₂_interval_le (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    hausdorffDist₂ Z.construct Z.interval.construct ≤ ∑ p, ‖Z.G p‖₂ := by -- --- PROOF ---
  have hr : (0 : ℝ) ≤ ∑ p, ‖Z.G p‖₂ := Finset.sum_nonneg fun _ _ => norm₂_nonneg _
  refine hausdorffDist₂_le_of_mem_dist hr
    (fun x hx => ⟨x, Z.interval_contains hx, by rw [sub_self, norm₂_zero]; exact hr⟩) ?_
  -- the other way the box is reached from the center, which the zonotope holds
  intro x hx
  exact ⟨Z.c, Z.center_mem_construct, aux_norm₂_sub_center_le hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
