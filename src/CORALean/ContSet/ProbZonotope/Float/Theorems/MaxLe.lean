module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Max
public import CORALean.ContSet.ProbZonotope.Real.Operations.Max
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

@[expose] public section

/-!
# The real `max` is under the float `max`

For every symmetric `Σ` of the covariance interval, when the float `max` returns `v`: `det(Σ)` is
positive and the real `max(probZ, m)`, `1 / ((2π)^{n/2} det(Σ)^{1/2}) · exp(-m²/2)`, is at most
`v`. An upper bound, not the value: `det(Σ)` is bounded below by `gⁿ`, `g` the Gershgorin bound
under every eigenvalue (`aux_pow_le_det`), and every other step is rounded the safe way.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic
open scoped _root_.Real

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A symmetric matrix whose Gershgorin discs lie right of `g ≥ 0` has determinant at least
`gⁿ`: every eigenvalue lies in a disc, and the determinant is their product. -/
theorem ProbZonotope.aux_pow_le_det {S : Mat ℝ n n} (hS : S.IsHermitian) {g : ℝ} (hg0 : 0 ≤ g)
    (hg : ∀ i, g ≤ S i i - ∑ j ∈ Finset.univ.erase i, |S i j|) :
    g ^ n ≤ S.det := by -- --- PROOF ---
  have hev : ∀ i, g ≤ hS.eigenvalues i := by
    intro i
    have hsp := hS.eigenvalues_mem_spectrum_real i
    rw [← Matrix.spectrum_toLin'] at hsp
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hsp)
    rw [Metric.mem_closedBall, Real.dist_eq] at hk
    simp only [Real.norm_eq_abs] at hk
    have := hg k
    linarith [(abs_le.mp hk).1]
  rw [hS.det_eq_prod_eigenvalues]
  calc g ^ n = ∏ _i : Fin n, g := by simp
    _ ≤ ∏ i, hS.eigenvalues i := Finset.prod_le_prod (fun _ _ => hg0) (fun i _ => hev i)
    _ = ∏ i, (hS.eigenvalues i : ℝ) := rfl

/-- The core: from the bounds of the computed quantities to the bound on the real `max`. -/
theorem ProbZonotope.aux_max_le_of_bounds {S : Mat ℝ n n} (hS : S.IsHermitian)
    (Z : Real.Zonotope (Vec ℝ n)) (m : ℝ) {g twoPi q d e : 𝕋} (hg : 0 < toReal g)
    (hgS : ∀ i, toReal g ≤ S i i - ∑ j ∈ Finset.univ.erase i, |S i j|)
    (htp : toReal twoPi ≤ 2 * π) (hq0 : 0 ≤ toReal q) (hq : toReal q ≤ toReal twoPi * toReal g)
    (hd : toReal d ≤ Real.sqrt (toReal q ^ n)) (hd0 : 0 < toReal d)
    (he : Real.exp (-(1 / 2) * m ^ 2) ≤ toReal e) : -- --- CONCL ---
    0 < S.det ∧
      (⟨Z, S⟩ : Real.ProbZonotope n).max m ≤ toReal (divUp e d) := by -- --- PROOF ---
  have hdet := ProbZonotope.aux_pow_le_det hS hg.le hgS
  have hdet0 : 0 < S.det := lt_of_lt_of_le (pow_pos hg n) hdet
  refine ⟨hdet0, ?_⟩
  have h2π : (0 : ℝ) < 2 * π := by positivity
  -- the denominator: `d ≤ √((2π g)ⁿ) ≤ √((2π)ⁿ det Σ) = (2π)^{n/2} det(Σ)^{1/2}`
  have hq' : toReal q ≤ 2 * π * toReal g :=
    le_trans hq (mul_le_mul_of_nonneg_right htp hg.le)
  have hqn : toReal q ^ n ≤ (2 * π) ^ n * S.det := by
    calc toReal q ^ n ≤ (2 * π * toReal g) ^ n := pow_le_pow_left₀ hq0 hq' n
      _ = (2 * π) ^ n * toReal g ^ n := mul_pow _ _ _
      _ ≤ (2 * π) ^ n * S.det := mul_le_mul_of_nonneg_left hdet (by positivity)
  have hD : Real.sqrt ((2 * π) ^ n * S.det)
      = (2 * π) ^ ((n : ℝ) / 2) * S.det ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul h2π.le]
    ring_nf
  have hdD : toReal d ≤ (2 * π) ^ ((n : ℝ) / 2) * S.det ^ ((1 : ℝ) / 2) :=
    hD ▸ le_trans hd (Real.sqrt_le_sqrt hqn)
  -- the quotient
  show 1 / ((2 * π) ^ ((n : ℝ) / 2) * S.det ^ ((1 : ℝ) / 2)) * Real.exp (-(1 / 2) * m ^ 2)
    ≤ toReal (divUp e d)
  rw [one_div_mul_eq_div]
  calc Real.exp (-(1 / 2) * m ^ 2) / ((2 * π) ^ ((n : ℝ) / 2) * S.det ^ ((1 : ℝ) / 2))
      ≤ Real.exp (-(1 / 2) * m ^ 2) / toReal d :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hd0 hdD
    _ ≤ toReal e / toReal d := div_le_div_of_nonneg_right he hd0.le
    _ ≤ toReal (divUp e d) := div_le_divUp e d hd0


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.max_le (P : ProbZonotope 𝕋 n) (m : 𝕋) (p k : ℕ) (Z : Real.Zonotope (Vec ℝ n))
    {S : Mat ℝ n n} (hS : S ∈ P.cov.construct) (hSh : S.IsHermitian) :
    ∀ v ∈ P.max m p k,
      0 < S.det ∧ (⟨Z, S⟩ : Real.ProbZonotope n).max (toReal m) ≤ toReal v := by -- --- PROOF ---
  intro v (hv : P.max m p k = some v)
  rw [ProbZonotope.max] at hv
  dsimp only at hv
  split_ifs at hv with hc
  obtain rfl := Option.some.inj hv
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hg, hq0⟩, hd0⟩ := hc
  have hg' := toReal_lt_of_ltStrict hg
  have hd0' := toReal_lt_of_ltStrict hd0
  have hq0' := toReal_le_of_le hq0
  rw [toReal_zero] at hg' hd0' hq0'
  have hS' := Interval.mem_mat_iff.mp hS
  refine ProbZonotope.aux_max_le_of_bounds hSh Z (toReal m) hg' ?_ ?_ hq0'
    (mulDown_le_mul _ _) ?_ hd0' ?_
  · -- the Gershgorin bound, row by row
    intro i
    refine le_trans (minimumOver_le _ i) (le_trans (subDown_le_sub _ _) ?_)
    have hsum : ∑ j ∈ Finset.univ.erase i, |S i j|
        ≤ ∑ j, toReal (if j = i then (zero : 𝕋)
            else maximum (absolute (P.cov.inf i j)) (absolute (P.cov.sup i j))) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, toReal_zero, zero_add]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [if_neg (Finset.ne_of_mem_erase hj), toReal_maximum, toReal_absolute,
        toReal_absolute]
      exact abs_le_max_abs_abs (hS' i j).1 (hS' i j).2
    linarith [(hS' i i).1, sum_le_sumUp fun j : Fin n => if j = i then (zero : 𝕋)
      else maximum (absolute (P.cov.inf i j)) (absolute (P.cov.sup i j))]
  · -- `2π` from below: four times `acosDown 0 ≤ π / 2`
    have hh : toReal (acosDown p k (zero : 𝕋)) ≤ π / 2 := by
      have := acosDown_le p k (zero : 𝕋)
      rwa [toReal_zero, Real.arccos_zero] at this
    have h1 := addDown_le_add (acosDown p k (zero : 𝕋)) (acosDown p k zero)
    have h2 := addDown_le_add (addDown (acosDown p k (zero : 𝕋)) (acosDown p k zero))
      (addDown (acosDown p k (zero : 𝕋)) (acosDown p k zero))
    linarith
  · -- the root of the power, from below
    exact le_trans (sqrtDown_le p _) (Real.sqrt_le_sqrt (powDown_le hq0' le_rfl n))
  · -- `exp(-m²/2)` from above
    have hmm := mulDown_le_mul m m
    have ha : toReal (neg (half (maximum zero (mulDown m m))))
        = -(Max.max 0 (toReal (mulDown m m)) / 2) := by
      rw [toReal_neg, toReal_half, toReal_maximum, toReal_zero]
    have hmax : Max.max 0 (toReal (mulDown m m)) ≤ toReal m ^ 2 :=
      _root_.max_le (sq_nonneg _) (by nlinarith)
    have hle := le_expUp k (neg (half (maximum zero (mulDown m m))))
      (by rw [ha]; have : (0 : ℝ) ≤ 2 ^ k / 2 := by positivity
          linarith [le_max_left 0 (toReal (mulDown m m))])
    refine le_trans (Real.exp_le_exp.mpr ?_) hle
    rw [ha]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
