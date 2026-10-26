module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.Global.EuclideanHausdorffDist
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The `ω_max` bound on how far a zonotope's box can be from the zonotope

[1, Thm. 1]'s `ω_max`, at the `‖·‖₂` the paper states it in, beside
`Zonotope.hausdorffDist₂_interval_le` (`ω_rad`); the same bound, unnamed, is [2, Thm. 3.2]. [2]'s
Eq. (15) misprints the selector as `k ≠ i*` for `i ≠ i*`; followed here. `aux_ghat` is the paper's
`ĝ`: a generator's entrywise magnitude with its first `‖·‖_∞`-attaining entry zeroed. The witness
is the paper's: each generator is taken at the coefficient that cancels the displacement exactly
in the entry `ĝ` zeroes, leaving at most twice the generator's magnitude in every other entry.
Soundness never uses that the zeroed entry is the largest, only that one entry is zeroed.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the Hausdorff distance to the box is at most twice the trimmed sum

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
* [2] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
      Analysis of Nonlinear Systems". Proceedings of the 24th International Conference on Hybrid
      Systems: Computation and Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1, Thm. 1]'s `ĝ`: the entrywise magnitude, zeroed at the first entry
attaining `‖·‖_∞`. -/
noncomputable def aux_ghat (v : Vec ℝ n) : Vec ℝ n :=
  fun i => if (∀ j, |v j| ≤ |v i|) ∧ ∀ j < i, |v j| < |v i| then 0 else |v i|

/-- A coordinatewise bound against twice a vector is a `‖·‖₂` bound against
twice its norm. -/
private theorem aux_norm₂_le_two_mul {r z : Vec ℝ n} (h : ∀ i, |r i| ≤ 2 * z i) : -- --- CONCL ---
    ‖r‖₂ ≤ 2 * ‖z‖₂ := by -- --- PROOF ---
  have key : ∑ i, r i ^ 2 ≤ ∑ i, (2 * z i) ^ 2 := Finset.sum_le_sum fun i _ => by
    have hi := mul_self_le_mul_self (abs_nonneg (r i)) (h i)
    rwa [abs_mul_abs_self, ← pow_two, ← pow_two] at hi
  -- the constant comes back out of the square root at the end
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  calc ‖r‖₂ = Real.sqrt (∑ i, r i ^ 2) := rfl
    _ ≤ Real.sqrt (∑ i, (2 * z i) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt (4 * ∑ i, z i ^ 2) := by
        rw [Finset.mul_sum]
        exact congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => by ring)
    _ = 2 * ‖z‖₂ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]; rfl

/-- One generator at the coefficient that cancels the displacement in the entry
`aux_ghat` zeroes: what is left is at most twice `ĝ` in every entry. -/
private theorem aux_exists_coeff (g lam : Vec ℝ n) (hlam : ∀ i, |lam i| ≤ 1) : -- --- CONCL ---
    ∃ a : ℝ, |a| ≤ 1 ∧ ∀ i, |lam i * |g i| - a * g i| ≤ 2 * aux_ghat g i := by -- --- PROOF ---
  by_cases hex : ∃ i₀ : Fin n, (∀ j, |g j| ≤ |g i₀|) ∧ ∀ j < i₀, |g j| < |g i₀|
  · obtain ⟨i₀, hmax, hfirst⟩ := hex
    -- the coefficient that cancels the generator in its own largest entry
    obtain ⟨a, ha1, ha2⟩ : ∃ a : ℝ, |a| ≤ 1 ∧ a * g i₀ = lam i₀ * |g i₀| := by
      by_cases h0 : g i₀ = 0
      · exact ⟨0, by norm_num, by rw [h0]; simp⟩
      · refine ⟨lam i₀ * |g i₀| / g i₀, ?_, by field_simp⟩
        rw [abs_div, abs_mul, abs_abs, mul_div_assoc, div_self (abs_ne_zero.mpr h0), mul_one]
        exact hlam i₀
    refine ⟨a, ha1, fun i => ?_⟩
    by_cases hi : i = i₀
    -- at the zeroed entry both sides are `0`
    · have hz : aux_ghat g i₀ = 0 := by
        simp only [aux_ghat]
        rw [if_pos ⟨hmax, hfirst⟩]
      rw [hi, ha2, sub_self, abs_zero, hz, mul_zero]
    -- everywhere else `ĝ` is the magnitude itself, and both terms are under it
    · have hgi : aux_ghat g i = |g i| := by
        simp only [aux_ghat]
        refine if_neg fun hp => hi ?_
        rcases lt_trichotomy i i₀ with h | h | h
        · exact absurd (hp.1 i₀) (not_le.mpr (hfirst i h))
        · exact h
        · exact absurd (hmax i) (not_le.mpr (hp.2 i₀ h))
      have h1 : |lam i * |g i| - a * g i| ≤ abs (lam i * |g i|) + |a * g i| := by
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
      have e1 : abs (lam i * |g i|) ≤ |g i| := by
        rw [abs_mul, abs_abs]
        nlinarith [hlam i, abs_nonneg (g i), abs_nonneg (lam i)]
      have e2 : |a * g i| ≤ |g i| := by
        rw [abs_mul]
        nlinarith [ha1, abs_nonneg (g i), abs_nonneg a]
      rw [hgi]
      linarith
  -- no maximal entry at all: `ĝ` zeroes nothing, and the zero coefficient works
  · refine ⟨0, by norm_num, fun i => ?_⟩
    have hg : aux_ghat g i = |g i| := by
      simp only [aux_ghat]
      exact if_neg fun hp => hex ⟨i, hp⟩
    rw [hg, zero_mul, sub_zero, abs_mul, abs_abs]
    nlinarith [hlam i, abs_nonneg (g i), abs_nonneg (lam i)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1] and [2, Thm. 3.2], the `ω_max` bound: the box is never further
from the zonotope than twice the generators' trimmed magnitudes reach, at
`‖·‖₂`. -/
theorem Zonotope.hausdorffDist₂_interval_le_max (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    hausdorffDist₂ Z.construct Z.interval.construct
      ≤ 2 * ‖∑ p, aux_ghat (Z.G p)‖₂ := by -- --- PROOF ---
  have hr : (0 : ℝ) ≤ 2 * ‖∑ p, aux_ghat (Z.G p)‖₂ := by
    have := norm₂_nonneg (∑ p, aux_ghat (Z.G p))
    linarith
  refine hausdorffDist₂_le_of_mem_dist hr
    (fun x hx => ⟨x, Z.interval_contains hx, by rw [sub_self, norm₂_zero]; exact hr⟩) ?_
  intro x hx
  -- a box point is within the columnwise magnitude sum of the center
  have hbox : ∀ i, |x i - Z.c i| ≤ ∑ p, |Z.G p i| := by
    intro i
    have hb := hx i
    simp only [Zonotope.interval, entry_ofEntry] at hb
    show |entry x i - entry Z.c i| ≤ ∑ p, |entry (Z.G p) i|
    rw [abs_le]
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  -- one coefficient per coordinate, guarded where the box degenerates to a point
  have hlamex : ∀ i : Fin n, ∃ t : ℝ, |t| ≤ 1 ∧ x i - Z.c i = t * ∑ p, |Z.G p i| := by
    intro i
    by_cases h : (∑ p, |Z.G p i|) = 0
    · have hz : x i - Z.c i = 0 := by
        have hb := hbox i
        rw [h] at hb
        exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
      exact ⟨0, by norm_num, by rw [hz, zero_mul]⟩
    · have hpos : 0 < ∑ p, |Z.G p i| :=
        lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Ne.symm h)
      refine ⟨(x i - Z.c i) / ∑ p, |Z.G p i|, ?_, by field_simp⟩
      rw [abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).mpr (hbox i)
  choose lam hlam1 hlam2 using hlamex
  -- one coefficient per generator, from the per-generator bound
  choose α hα1 hα2 using fun p => aux_exists_coeff (Z.G p) lam hlam1
  refine ⟨Z.c + ∑ p, α p • Z.G p, ⟨α, hα1, rfl⟩, ?_⟩
  refine aux_norm₂_le_two_mul fun i => ?_
  -- the residual is the generators' own residuals, summed
  have hsum : ∑ p, Z.G p i * α p = ∑ p, α p * Z.G p i :=
    Finset.sum_congr rfl fun p _ => mul_comm _ _
  have hres : (x - (Z.c + ∑ p, α p • Z.G p)) i
      = ∑ p, (lam i * |Z.G p i| - α p * Z.G p i) := by
    show x i - (Z.c + ∑ p, α p • Z.G p) i = _
    rw [Entrywise.add_sum_smul_apply, hsum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hlam2 i]
    ring
  rw [hres, show (∑ p, aux_ghat (Z.G p)) i = ∑ p, aux_ghat (Z.G p) i from
    Finset.sum_apply i Finset.univ _, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hα2 p i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
