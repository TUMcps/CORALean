import CORALean.NN.Layers.Theorems.Real.SShapeBandSound
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# DeepZ's S-shape band has the least area of its family

[1, Thm. 3.2], the optimality half: among the bands of [1, Fig. 2], the lines of slope `λ`
through `(l, f(l))` and `(u, f(u))`, every sound one has `λ ≤ min(f'(l), f'(u))`, the slope of
the lower line being at most the right derivative at `l` and that of the upper one at most the
left derivative at `u`. Its area [1, Eq. 6], `(f(u) - f(l) - λ (u - l)) (u - l)`, falls as `λ`
grows, so `λ_opt = min(f'(l), f'(u))` has the least area, and `sShape_band_sound` is that it is
sound when `f'` rises and then falls.

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Filter Topology


-- =======================================  MAIN THEOREM  ======================================= --

theorem sShape_band_area_le {f : ℝ → ℝ} {dfl dfu lam l u : ℝ} (hlu : l < u)
    (hdl : HasDerivAt f dfl l) (hdu : HasDerivAt f dfu u)
    (hband : ∀ t, l ≤ t → t ≤ u → f l + lam * (t - l) ≤ f t ∧ f t ≤ f u + lam * (t - u)) :
    (f u - f l - min dfl dfu * (u - l)) * (u - l)
      ≤ (f u - f l - lam * (u - l)) * (u - l) := by -- --- PROOF ---
  -- the lower line's slope is at most the right derivative at `l`
  have hl : lam ≤ dfl := by
    refine ge_of_tendsto ((hasDerivAt_iff_tendsto_slope_left_right.mp hdl).2) ?_
    filter_upwards [Ioo_mem_nhdsGT hlu] with t ht
    have h := (hband t ht.1.le ht.2.le).1
    rw [slope_def_field, le_div_iff₀ (by linarith [ht.1])]
    linarith
  -- and the upper line's at most the left derivative at `u`
  have hu : lam ≤ dfu := by
    refine ge_of_tendsto ((hasDerivAt_iff_tendsto_slope_left_right.mp hdu).1) ?_
    filter_upwards [Ioo_mem_nhdsLT hlu] with t ht
    have h := (hband t ht.1.le ht.2.le).2
    rw [slope_def_field, ← neg_div_neg_eq, le_div_iff₀ (by linarith [ht.2])]
    linarith
  have hw : 0 ≤ u - l := by linarith
  have hm : lam ≤ min dfl dfu := le_min hl hu
  nlinarith [mul_le_mul_of_nonneg_right hm hw]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
