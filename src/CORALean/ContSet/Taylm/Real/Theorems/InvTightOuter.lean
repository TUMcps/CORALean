module

public import CORALean.ContSet.Taylm.Real.Operations.InvTight
public import CORALean.ContSet.Taylm.Real.Theorems.InvSubSumEq
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import CORALean.ContSet.Taylm.Real.Theorems.ComposeOuter
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem

@[expose] public section

/-!
# `Taylm.invTight` encloses `1 / f`

[1, Eq. 38] keeps a sound remainder in either branch: on the box, `1/f` minus the expansion is
`(-1)ᴺ⁺¹ (f - c)ᴺ⁺¹ / (f cᴺ⁺¹)` exactly (`inv_sub_sum_eq`), at most `rᴺ⁺¹/(m |c|ᴺ⁺¹)`, the exact
bound, which is at most the Lagrange one since `|c| ≥ m`.

## Inputs
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function
* `hside` – the range stays on one side of zero

## Conclusion
* the result encloses the reciprocal of the function

## References

* [1] M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Taylor coefficients of `1/x`. -/
theorem Taylm.aux_inv_coef (c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => x⁻¹) c / (k.factorial : ℝ) = (-1) ^ k / c ^ (k + 1) := by
  rw [iteratedDeriv_eq_iterate, show (fun x : ℝ => x⁻¹) = Inv.inv from rfl, iter_deriv_inv]
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  field_simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.invTight_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hside : 0 < min T.constCoef T.bounds.inf ∨ max T.constCoef T.bounds.sup < 0) : -- --- CONCL ---
    T.invTight.Encloses fun t => (f t)⁻¹ := by -- --- PROOF ---
  set c := T.constCoef
  set N := T.maxOrder
  set lo := min c T.bounds.inf
  set hi := max c T.bounds.sup
  set m := max lo (-hi)
  set r := T.reach c
  -- every point of the hull is at least `m` away from zero, and `m > 0`
  have hm : ∀ ξ ∈ Set.Icc lo hi, 0 < m ∧ m ≤ |ξ| := by
    intro ξ hξ
    rcases hside with hpos | hneg
    · have : m = lo := max_eq_left (by linarith [hξ.1, hξ.2])
      rw [this, abs_of_pos (lt_of_lt_of_le hpos hξ.1)]
      exact ⟨hpos, hξ.1⟩
    · have : m = -hi := max_eq_right (by linarith [hξ.1, hξ.2])
      rw [this, abs_of_neg (lt_of_le_of_lt hξ.2 hneg)]
      exact ⟨by linarith, by linarith [hξ.2]⟩
  have hcm := hm c ⟨min_le_left _ _, le_max_left _ _⟩
  have hc0 : c ≠ 0 := abs_pos.1 (lt_of_lt_of_le hcm.1 hcm.2)
  refine Taylm.compose_outer h _ _ _ _ _ fun t ht => ?_
  have hb := Taylm.bounds_mem h ht
  have hfm := hm (f t) ⟨le_trans (min_le_right _ _) hb.1, le_trans hb.2 (le_max_right _ _)⟩
  have hf0 : f t ≠ 0 := abs_pos.1 (lt_of_lt_of_le hfm.1 hfm.2)
  -- `|f - c| ≤ reach`
  have hy : |f t - c| ≤ r := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (T.bounds.inf - c)
      have := le_max_left |T.bounds.inf - c| |T.bounds.sup - c|
      simp only [r, Taylm.reach]; linarith [hb.1]
    · have := le_abs_self (T.bounds.sup - c)
      have := le_max_right |T.bounds.inf - c| |T.bounds.sup - c|
      simp only [r, Taylm.reach]; linarith [hb.2]
  -- the exact remainder, and its magnitude
  simp only [Taylm.aux_inv_coef, div_mul_eq_mul_div]
  rw [Taylm.inv_sub_sum_eq (c := T.constCoef) hc0 hf0, abs_div, abs_mul, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_pow, abs_pow]
  have hr0 : 0 ≤ r := le_trans (abs_nonneg _) hy
  have hR : |f t - c| ^ (N + 1) / (|f t| * |c| ^ (N + 1)) ≤ r ^ (N + 1) / (m * |c| ^ (N + 1)) := by
    have hc1 : 0 < |c| ^ (N + 1) := pow_pos (abs_pos.2 hc0) _
    exact div_le_div₀ (pow_nonneg hr0 _) (pow_le_pow_left₀ (abs_nonneg _) hy _)
      (mul_pos hcm.1 hc1) (mul_le_mul_of_nonneg_right hfm.2 hc1.le)
  have hL : r ^ (N + 1) / (m * |c| ^ (N + 1)) ≤ r ^ (N + 1) / m ^ (N + 2) := by
    refine div_le_div_of_nonneg_left (pow_nonneg hr0 _) (pow_pos hcm.1 _) ?_
    rw [pow_succ' m (N + 1)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcm.1.le hcm.2 _) hcm.1.le
  split_ifs
  · exact hR
  · exact le_trans hR hL

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
