import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.Global.EuclideanHausdorffDist

/-!
# The `ω_cut` bound on how far a zonotope's box can be from the zonotope

[1, Thm. 1]'s `ω_cut`, at the `‖·‖₂` the paper states it in, beside
`Zonotope.hausdorffDist₂_interval_le` and `_le_max`, the same theorem's other two.

Each generator is taken at the coefficient that projects the displacement onto
it, so what is left of that generator's share is what the projection cuts off.
The paper reaches the bound through the Bauer maximum principle; `aux_sq_bound`
replaces that by an identity — `‖g‖₂² Σᵢ νᵢ²gᵢ² - (Σᵢ νᵢgᵢ²)²` is half the
double sum `Σᵢⱼ gᵢ²gⱼ²(νᵢ-νⱼ)²`, whose diagonal vanishes — so the estimate
`(νᵢ-νⱼ)² ≤ 4` off the diagonal gives the bound over the whole coefficient box
rather than over its vertices, and no convexity argument is needed.

A generator of length zero divides by zero in the printed formula, which in Lean
is `0`, and the bound reads `0 ≤ 0` there: the case is real but needs no guard.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability
      Algorithms for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear
      Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
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

/-- What the projection leaves of a generator, before dividing by its length:
the symmetrised double sum, whose diagonal drops out. -/
theorem aux_sq_bound (g nu : Vec ℝ n) (hnu : ∀ i, |nu i| ≤ 1) :
    (∑ i, g i ^ 2) * (∑ i, nu i ^ 2 * g i ^ 2) - (∑ i, nu i * g i ^ 2) ^ 2
      ≤ 2 * ((∑ i, g i ^ 2) ^ 2 - ∑ i, g i ^ 4) := by -- --- PROOF ---
  -- the double sum of squared coefficient differences is twice the left side
  have hid : ∑ i, ∑ j, g i ^ 2 * g j ^ 2 * (nu i - nu j) ^ 2
      = 2 * ((∑ i, g i ^ 2) * (∑ i, nu i ^ 2 * g i ^ 2) - (∑ i, nu i * g i ^ 2) ^ 2) := by
    have hinner : ∀ i : Fin n, ∑ j, g i ^ 2 * g j ^ 2 * (nu i - nu j) ^ 2
        = nu i ^ 2 * g i ^ 2 * (∑ j, g j ^ 2) - nu i * g i ^ 2 * (2 * ∑ j, nu j * g j ^ 2)
          + g i ^ 2 * (∑ j, nu j ^ 2 * g j ^ 2) := by
      intro i
      have hterm : ∀ j : Fin n, g i ^ 2 * g j ^ 2 * (nu i - nu j) ^ 2
          = nu i ^ 2 * g i ^ 2 * g j ^ 2 - nu i * g i ^ 2 * (2 * (nu j * g j ^ 2))
            + g i ^ 2 * (nu j ^ 2 * g j ^ 2) := fun j => by ring
      simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [hinner, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  -- off the diagonal a squared difference of coefficients is at most `4`
  have hle : ∀ i : Fin n, ∑ j, g i ^ 2 * g j ^ 2 * (nu i - nu j) ^ 2
      ≤ 4 * (g i ^ 2 * (∑ j, g j ^ 2) - g i ^ 2 * g i ^ 2) := by
    intro i
    have hsplit : ∑ j, g i ^ 2 * g j ^ 2 * (nu i - nu j) ^ 2
        = ∑ j ∈ Finset.univ.erase i, g i ^ 2 * g j ^ 2 * (nu i - nu j) ^ 2 := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      simp
    rw [hsplit]
    have hstep : ∑ j ∈ Finset.univ.erase i, g i ^ 2 * g j ^ 2 * (nu i - nu j) ^ 2
        ≤ ∑ j ∈ Finset.univ.erase i, 4 * (g i ^ 2 * g j ^ 2) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have h1 := abs_le.mp (hnu i)
      have h2 := abs_le.mp (hnu j)
      have hd : (nu i - nu j) ^ 2 ≤ 4 := by nlinarith [h1.1, h1.2, h2.1, h2.2]
      nlinarith [mul_nonneg (sq_nonneg (g i)) (sq_nonneg (g j)), hd, sq_nonneg (nu i - nu j)]
    refine hstep.trans_eq ?_
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  -- summing the per-row bound closes the gap between the two sides
  have htot : ∑ i, (4 : ℝ) * (g i ^ 2 * (∑ j, g j ^ 2) - g i ^ 2 * g i ^ 2)
      = 4 * ((∑ i, g i ^ 2) ^ 2 - ∑ i, g i ^ 4) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul,
      show ∑ i, g i ^ 2 * g i ^ 2 = ∑ i, g i ^ 4 from Finset.sum_congr rfl fun i _ => by ring]
    ring
  have := (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hle i).trans_eq htot
  rw [hid] at this
  linarith

/-- One generator taken at the coefficient that projects the displacement onto
it: what the projection cuts off is the paper's per-generator term. -/
theorem aux_exists_coeff_cut (g lam : Vec ℝ n) (hlam : ∀ i, |lam i| ≤ 1) :
    ∃ a : ℝ, |a| ≤ 1 ∧ ‖(fun i => lam i * |g i| - a * g i : Vec ℝ n)‖₂
      ≤ Real.sqrt 2 * (‖g‖₂ * Real.sqrt (1 - (∑ i, g i ^ 4) / ‖g‖₂ ^ 4)) := by -- --- PROOF ---
  have hrnn : 0 ≤ Real.sqrt 2 * (‖g‖₂ * Real.sqrt (1 - (∑ i, g i ^ 4) / ‖g‖₂ ^ 4)) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm₂_nonneg g) (Real.sqrt_nonneg _))
  -- the displacement read along the generator rather than against its magnitude
  have hnuex : ∀ i : Fin n, ∃ t : ℝ, |t| ≤ 1 ∧ t * g i = lam i * |g i| := by
    intro i
    by_cases h : g i = 0
    · exact ⟨0, by norm_num, by rw [h]; simp⟩
    · refine ⟨lam i * |g i| / g i, ?_, by field_simp⟩
      rw [abs_div, abs_mul, abs_abs, mul_div_assoc, div_self (abs_ne_zero.mpr h), mul_one]
      exact hlam i
  choose nu hnu1 hnug using hnuex
  by_cases hT : (∑ i, g i ^ 2) = 0
  -- a generator of length zero has nothing to cancel and nothing to leave
  · refine ⟨0, by norm_num, ?_⟩
    have hg : ∀ i, g i = 0 := fun i => sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
      fun i _ => sq_nonneg (g i)).mp hT i (Finset.mem_univ i))
    have hz : ∑ i, (lam i * |g i| - 0 * g i) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hg i]; simp
    show Real.sqrt (∑ i, (lam i * |g i| - 0 * g i) ^ 2) ≤ _
    rw [hz, Real.sqrt_zero]
    exact hrnn
  · have hTpos : 0 < ∑ i, g i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hT)
    refine ⟨(∑ i, nu i * g i ^ 2) / ∑ i, g i ^ 2, ?_, ?_⟩
    -- the projection coefficient stays in `[-1, 1]`, the generator being longest
    · rw [abs_div, abs_of_pos hTpos]
      refine (div_le_one hTpos).mpr ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (sq_nonneg (g i))]
      nlinarith [hnu1 i, sq_nonneg (g i), abs_nonneg (nu i)]
    · -- what the projection leaves, written as one quotient by the squared length
      have hsq : ∑ i, (lam i * |g i| - (∑ i, nu i * g i ^ 2) / (∑ i, g i ^ 2) * g i) ^ 2
          = ((∑ i, g i ^ 2) * (∑ i, nu i ^ 2 * g i ^ 2) - (∑ i, nu i * g i ^ 2) ^ 2)
            / ∑ i, g i ^ 2 := by
        -- the square expanded against the projection, before the quotient is formed
        have hexp : ∑ i, (lam i * |g i| - (∑ i, nu i * g i ^ 2) / (∑ i, g i ^ 2) * g i) ^ 2
            = (∑ i, nu i ^ 2 * g i ^ 2)
              - 2 * ((∑ i, nu i * g i ^ 2) / ∑ i, g i ^ 2) * (∑ i, nu i * g i ^ 2)
              + ((∑ i, nu i * g i ^ 2) / ∑ i, g i ^ 2) ^ 2 * ∑ i, g i ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by rw [← hnug i]; ring
        rw [hexp]
        field_simp
        ring
      -- the printed formula, squared, is that same quotient's bound
      have hn2 : ‖g‖₂ ^ 2 = ∑ i, g i ^ 2 := norm₂_sq g
      have hn4 : ‖g‖₂ ^ 4 = (∑ i, g i ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hn2]
      have hQ : (∑ i, g i ^ 4) ≤ (∑ i, g i ^ 2) ^ 2 := by
        refine le_trans (le_of_eq ?_) (Finset.sum_sq_le_sq_sum_of_nonneg
          fun i _ => sq_nonneg (g i))
        exact Finset.sum_congr rfl fun i _ => by ring
      have hfrac : (0 : ℝ) ≤ 1 - (∑ i, g i ^ 4) / ‖g‖₂ ^ 4 := by
        rw [hn4, sub_nonneg]
        exact (div_le_one (by positivity)).mpr hQ
      have hrhs : (Real.sqrt 2 * (‖g‖₂ * Real.sqrt (1 - (∑ i, g i ^ 4) / ‖g‖₂ ^ 4))) ^ 2
          = 2 * ((∑ i, g i ^ 2) ^ 2 - ∑ i, g i ^ 4) / ∑ i, g i ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sq_sqrt hfrac, hn2, hn4]
        field_simp
      -- both sides are non-negative, so the comparison happens under the square root
      show Real.sqrt (∑ i, (lam i * |g i| - (∑ i, nu i * g i ^ 2) / (∑ i, g i ^ 2) * g i) ^ 2) ≤ _
      rw [← Real.sqrt_sq hrnn]
      refine Real.sqrt_le_sqrt ?_
      rw [hsq, hrhs]
      gcongr
      exact aux_sq_bound g nu hnu1


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], the `ω_cut` bound: the box is never further from the zonotope
than what projecting onto each generator in turn cuts off, at `‖·‖₂`. -/
theorem Zonotope.hausdorffDist₂_interval_le_cut (Z : Zonotope (Vec ℝ n)) :
    hausdorffDist₂ Z.construct Z.interval.construct
      ≤ Real.sqrt 2 * ∑ p, ‖Z.G p‖₂
          * Real.sqrt (1 - (∑ i, Z.G p i ^ 4) / ‖Z.G p‖₂ ^ 4) := by -- --- PROOF ---
  have hr : (0 : ℝ) ≤ Real.sqrt 2 * ∑ p, ‖Z.G p‖₂
      * Real.sqrt (1 - (∑ i, Z.G p i ^ 4) / ‖Z.G p‖₂ ^ 4) :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun p _ =>
      mul_nonneg (norm₂_nonneg _) (Real.sqrt_nonneg _))
  refine hausdorffDist₂_le_of_mem_dist hr
    (fun x hx => ⟨x, Z.interval_contains hx, by rw [sub_self, norm₂_zero]; exact hr⟩) ?_
  intro x hx
  -- a box point is within the columnwise magnitude sum of the centre
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
  choose α hα1 hα2 using fun p => aux_exists_coeff_cut (Z.G p) lam hlam1
  refine ⟨Z.c + ∑ p, α p • Z.G p, ⟨α, hα1, rfl⟩, ?_⟩
  -- the residual is the generators' own residuals, summed
  have hres : x - (Z.c + ∑ p, α p • Z.G p)
      = ∑ p, (fun i => lam i * |Z.G p i| - α p * Z.G p i : Vec ℝ n) := by
    funext i
    have hsum : ∑ p, Z.G p i * α p = ∑ p, α p * Z.G p i :=
      Finset.sum_congr rfl fun p _ => mul_comm _ _
    show x i - (Z.c + ∑ p, α p • Z.G p) i
        = (∑ p, (fun i => lam i * |Z.G p i| - α p * Z.G p i : Vec ℝ n)) i
    rw [Entrywise.add_sum_smul_apply, hsum, Finset.sum_apply i Finset.univ _,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← hlam2 i]
    ring
  rw [hres]
  refine (norm₂_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ => hα2 p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
