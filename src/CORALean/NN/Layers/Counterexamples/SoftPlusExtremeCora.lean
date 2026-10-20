module

public import CORALean.NN.Layers.Definitions.Softplus
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `Layer.softplusErrorLowerCora`: the lower error of `nnSoftPlusLayer`'s batch enclosure

`computeExtremePointsBatch` (l. 65-77) gives `aux_imgEncBatch` the candidate extrema of `f(x) - m x`
after `m = min(tol,max(m,1-tol))`. As `max(m,1-tol) >= 1-tol > tol`, `m` is the constant `tol`, the
candidate `xs ≈ -18.4/k` lies outside every realistic `[l, u]` and gets deviation `inf`, so `el =
min(ds)` ignores the interior minimum `x = log(m/(1-m))/k` and is too large. Read from the source,
not run.

With `sharpness = 1` on `[-1, 1]` the chord slope is `1/2` and the deviation `f(x) - x/2` is `log 2
≈ 0.693` at `x = 0`, while CORA's `el` is the deviation at `l`, `0.813`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some point's deviation from the chord lies below CORA's lower error
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The candidate extremum `xs` of `computeExtremePointsBatch`, for the slope `m` and sharpness
`β`. -/
noncomputable def Layer.softplusExtremeCora (β m : ℝ) : ℝ :=
  let tol : ℝ := (10⁻¹ : ℝ) ^ 8
  let m' := min tol (max m (1 - tol))
  1 / β * Real.log (-m' / (m' - 1))

/-- The `el` of `aux_imgEncBatch` for `poly_method = 'bounds'` on `[l, u]` and sharpness `β`:
the least deviation `f(x) - m x` over the candidates `[xs, l]` inside the box. -/
noncomputable def Layer.softplusErrorLowerCora (β l u : ℝ) : ℝ :=
  -- m = (f(u) - f(l)) ./ (2*r)
  let m := (softplus β u - softplus β l) / (u - l)
  -- ds = f(xs) - m.*xs
  let ds : ℝ → ℝ := fun x => softplus β x - m * x
  let xs := Layer.softplusExtremeCora β m
  -- ds(xs < l | xs > u) = inf; el = min(ds)
  if l ≤ xs ∧ xs ≤ u then min (ds xs) (ds l) else ds l

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- At sharpness `1` on `[-1, 1]` there is a point whose deviation `f(x) - m x` is below CORA's
lower error `el`; `x = 0` is one. -/
theorem Layer.softplusExtreme_cora_counterexample : -- --- CONCL ---
    ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      softplus 1 x - (softplus 1 1 - softplus 1 (-1)) / (1 - (-1)) * x <
        Layer.softplusErrorLowerCora 1 (-1) 1 := by -- --- PROOF ---
  -- facts about `exp 1`
  have he1 : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hprod : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  have hie : (1 : ℝ) / 3 < Real.exp (-1) := by nlinarith [Real.exp_pos (-1)]
  -- log (1 + exp (-1)) = log (1 + exp 1) - 1
  have hL : Real.log (1 + Real.exp (-1)) = Real.log (1 + Real.exp 1) - 1 := by
    have h : 1 + Real.exp (-1) = (1 + Real.exp 1) / Real.exp 1 := by
      rw [Real.exp_neg]; field_simp; ring
    rw [h, Real.log_div (by positivity) (by positivity), Real.log_exp]
  have hm : (softplus 1 1 - softplus 1 (-1)) / (1 - (-1)) = 1 / 2 := by
    simp only [softplus, div_one, mul_neg, mul_one]
    rw [hL]; norm_num
  have htol : min ((10⁻¹ : ℝ) ^ 8) (max (1 / 2) (1 - (10⁻¹ : ℝ) ^ 8)) = (10⁻¹ : ℝ) ^ 8 := by
    rw [max_eq_right (by norm_num), min_eq_left (by norm_num)]
  -- the clamp returns `tol` for the slope `1/2`, so `xs = log (tol / (1 - tol))`
  have hx : Layer.softplusExtremeCora 1 (1 / 2) =
      Real.log ((10⁻¹ : ℝ) ^ 8 / (1 - (10⁻¹ : ℝ) ^ 8)) := by
    simp only [Layer.softplusExtremeCora]
    rw [htol, one_div_one, one_mul]
    congr 1
    have : ((10⁻¹ : ℝ) ^ 8 - 1) ≠ 0 := by norm_num
    have : (1 - (10⁻¹ : ℝ) ^ 8) ≠ 0 := by norm_num
    field_simp
    ring
  have hxs : Layer.softplusExtremeCora 1 (1 / 2) < -1 := by
    rw [hx, Real.log_lt_iff_lt_exp (by norm_num)]
    have : (10⁻¹ : ℝ) ^ 8 / (1 - (10⁻¹ : ℝ) ^ 8) < 1 / 3 := by norm_num
    linarith
  -- the point `0` is in the box, and `xs` is not
  refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
  have hel : Layer.softplusErrorLowerCora 1 (-1) 1 =
      softplus 1 (-1) - 1 / 2 * (-1) := by
    simp only [Layer.softplusErrorLowerCora, hm]
    rw [if_neg (by rintro ⟨h1, -⟩; linarith)]
  rw [hel, hm]
  -- log 2 < log (1 + exp (-1)) + 1/2 = log (1 + exp 1) - 1/2, as `2 exp (1/2) < 1 + exp 1`
  have hs : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hs1 : 1 < Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
  have hlt : 2 * Real.exp (1 / 2) < 1 + Real.exp 1 := by nlinarith
  have hlog : Real.log (2 * Real.exp (1 / 2)) < Real.log (1 + Real.exp 1) :=
    Real.log_lt_log (by positivity) hlt
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at hlog
  simp only [softplus, div_one, mul_neg, mul_one, mul_zero, Real.exp_zero]
  rw [hL]
  norm_num
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
