module

public import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# The exponential's expansion and its Lagrange term, as printed

[1, Def. 3 (exp)], eqs. 2.2-2.4: with `f̄ = f - c_f`,
`exp(f) = exp(c_f)·{1 + f̄ + … + f̄ᵏ/k! + f̄ᵏ⁺¹ exp(θf̄)/(k+1)!}` for some `θ ∈ [0, 1]`, and the
Lagrange term lies in `exp(c_f)·(B(P̄) + I)ᵏ⁺¹·exp([0, 1]·(B(P̄) + I))/(k+1)!`.

`B(P̄) + I` is the interval `J = [B₁ - c_f, B₂ - c_f]` from the model's own bounds
`Taylm.bounds`, which hold `f` (`Taylm.bounds_mem`), so `f̄(t) ∈ J` at every point of the box.
The interval products of the printed bound are read as the pointwise products of sets
(`open Pointwise`): interval arithmetic returns a superset of each, so the Lagrange term lying
in the set expression is the printed claim at its tightest. Every order `k` is covered, not
only the `k = n` that `Taylm.exp` uses.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Eq. 2.2 at one point: `exp(c + y)` is its degree-`k` expansion at `c` plus the Lagrange
term `exp(c)·yᵏ⁺¹ exp(θy)/(k+1)!` at some `θ ∈ [0, 1]`. -/
theorem Taylm.aux_exp_lagrange (c y : ℝ) (k : ℕ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      Real.exp (c + y) - Real.exp c * ∑ j ∈ Finset.range (k + 1), y ^ j / (j.factorial : ℝ)
        = Real.exp c * (y ^ (k + 1) * Real.exp (θ * y))
          / ((k + 1).factorial : ℝ) := by -- --- PROOF ---
  rcases eq_or_ne y 0 with rfl | hy
  · -- `y = 0`: only the constant term survives, and the Lagrange term is zero
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun j _ => by simp)]
    simp
  have hne : c ≠ c + y := by intro h; apply hy; linarith
  have hf : ContDiffOn ℝ (k + 1) Real.exp (Set.uIcc c (c + y)) :=
    Real.contDiff_exp.contDiffOn
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf
  have hu : UniqueDiffOn ℝ (Set.uIcc c (c + y)) := uniqueDiffOn_Icc (by
    rcases lt_or_gt_of_ne hne with h | h
    · simp [min_eq_left h.le, max_eq_right h.le, h]
    · simp [min_eq_right h.le, max_eq_left h.le, h])
  have hc : c ∈ Set.uIcc c (c + y) := Set.left_mem_uIcc
  -- every derivative of `exp` is `exp`
  have hder : ∀ j, iteratedDeriv j Real.exp = Real.exp := fun j => by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  -- the within-the-segment Taylor polynomial is `exp c` times the exponential series
  have htay : taylorWithinEval Real.exp k (Set.uIcc c (c + y)) c (c + y)
      = Real.exp c * ∑ j ∈ Finset.range (k + 1), y ^ j / (j.factorial : ℝ) := by
    rw [taylor_within_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (Real.contDiff_exp.contDiffAt) hc, hder,
      smul_eq_mul, add_sub_cancel_left]
    ring
  -- the mean-value point is `c + θ y` for `θ = (ξ - c) / y`, which lies in `[0, 1]`
  have hξ' : ξ ∈ Set.uIcc c (c + y) := Set.uIoo_subset_uIcc_self hξ
  refine ⟨(ξ - c) / y, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hy with hneg | hpos
    · rw [Set.uIcc_of_ge (by linarith)] at hξ'
      constructor
      · exact div_nonneg_of_nonpos (by linarith [hξ'.2]) hneg.le
      · rw [div_le_one_of_neg hneg]; linarith [hξ'.1]
    · rw [Set.uIcc_of_le (by linarith)] at hξ'
      constructor
      · exact div_nonneg (by linarith [hξ'.1]) hpos.le
      · rw [div_le_one hpos]; linarith [hξ'.2]
  · rw [← htay, h, hder, add_sub_cancel_left, div_mul_cancel₀ _ hy,
      show ξ = c + (ξ - c) by ring, Real.exp_add, add_sub_cancel_left]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 3 (exp)], eqs. 2.2-2.4: for a model `T` of `f`, at every point of the box the
exponential minus its degree-`k` expansion at `c_f` is the Lagrange term, and that lies in
`exp(c_f)·Jᵏ⁺¹·exp([0, 1]·J)/(k+1)!` for `J = B(P̄) + I`. -/
theorem Taylm.exp_lagrange_mem {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (k : ℕ)
    {t : Vec ℝ n} (ht : t ∈ Taylm.box n) :
    Real.exp (f t) - Real.exp T.constCoef
        * ∑ j ∈ Finset.range (k + 1), (f t - T.constCoef) ^ j / (j.factorial : ℝ)
      ∈ (fun r => Real.exp T.constCoef * r / ((k + 1).factorial : ℝ)) ''
          (Set.Icc (T.bounds.1 - T.constCoef) (T.bounds.2 - T.constCoef) ^ (k + 1)
            * Real.exp '' (Set.Icc (0 : ℝ) 1
              * Set.Icc (T.bounds.1 - T.constCoef)
                (T.bounds.2 - T.constCoef))) := by -- --- PROOF ---
  set c := T.constCoef
  set J := Set.Icc (T.bounds.1 - c) (T.bounds.2 - c)
  -- `f̄(t)` lies in `J`, the model's bounds holding `f`
  have hy : f t - c ∈ J := by
    obtain ⟨h1, h2⟩ := Taylm.bounds_mem h ht
    exact ⟨by linarith, by linarith⟩
  obtain ⟨θ, hθ, he⟩ := Taylm.aux_exp_lagrange c (f t - c) k
  have hft : Real.exp (f t) = Real.exp (c + (f t - c)) := by rw [add_sub_cancel]
  rw [hft, he]
  exact ⟨_, Set.mul_mem_mul (Set.pow_mem_pow hy)
    (Set.mem_image_of_mem _ (Set.mul_mem_mul hθ hy)), rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
