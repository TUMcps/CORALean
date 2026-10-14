module

public import CORALean.ContSet.VPolytope.Float.Operations.CenterBox
public import CORALean.ContSet.VPolytope.Float.Theorems.NominalEq
public import CORALean.ContSet.VPolytope.Real.Operations.Center
public import CORALean.ContSet.VPolytope.Real.Theorems.CenterMem

@[expose] public section

/-!
# The float centre box holds a point of the polytope

The exact mean of the nominal vertices lies in the box (each bound brackets the coordinate sum
divided by the count, whatever the sum's sign), and it is a point of the nominal polytope
(`center_mem`), so adding any point of the error box gives a point of the float polytope. Outer:
the box is not claimed to be the centre, only to hold it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `s / k` is above the smaller of `sD / kU` and `sD / kD` for `sD ≤ s` and `0 < kD ≤ k ≤ kU`. -/
theorem VPolytope.aux_div_ge {s sD k kD kU : ℝ} (hs : sD ≤ s) (hD : 0 < kD) (hDk : kD ≤ k)
    (hkU : k ≤ kU) : min (sD / kU) (sD / kD) ≤ s / k := by -- --- PROOF ---
  have hk : 0 < k := lt_of_lt_of_le hD hDk
  refine le_trans ?_ (div_le_div_of_nonneg_right hs hk.le)
  rcases le_total 0 sD with h | h
  · exact le_trans (min_le_left _ _) (div_le_div_of_nonneg_left h hk hkU)
  · refine le_trans (min_le_right _ _) ?_
    rw [div_le_div_iff₀ hD hk]
    nlinarith

/-- `s / k` is below the larger of `sU / kU` and `sU / kD` for `s ≤ sU` and `0 < kD ≤ k ≤ kU`. -/
theorem VPolytope.aux_div_le {s sU k kD kU : ℝ} (hs : s ≤ sU) (hD : 0 < kD) (hDk : kD ≤ k)
    (hkU : k ≤ kU) : s / k ≤ max (sU / kU) (sU / kD) := by -- --- PROOF ---
  have hk : 0 < k := lt_of_lt_of_le hD hDk
  have := VPolytope.aux_div_ge (s := -s) (sD := -sU) (neg_le_neg hs) hD hDk hkU
  rw [neg_div, neg_div, neg_div, min_le_iff] at this
  rcases this with h | h
  · exact le_trans (by linarith) (le_max_left _ _)
  · exact le_trans (by linarith) (le_max_right _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.centerBox_meets (P : VPolytope (Vec 𝕋 n)) (hk : 0 < P.k) :
    ∃ x ∈ P.centerBox.construct, {x} + P.I_error.construct ⊆ P.construct := by -- --- PROOF ---
  -- the exact mean of the nominal vertices
  refine ⟨(InflatedContSet.nominal P).center, ?_, ?_⟩
  · -- the two roundings of the count, the lower one floored at one
    have hU : (P.k : ℝ) ≤ toReal (nsmulUp P.k (one : 𝕋)) := by
      have := le_nsmulUp P.k (one : 𝕋); rwa [toReal_one, mul_one] at this
    have hD : toReal (nsmulDown P.k (one : 𝕋)) ≤ (P.k : ℝ) := by
      have := nsmulDown_le P.k (one : 𝕋); rwa [toReal_one, mul_one] at this
    have hk1 : (1 : ℝ) ≤ P.k := by exact_mod_cast hk
    have hm1 : (1 : ℝ) ≤ toReal (maximum one (nsmulDown P.k (one : 𝕋))) := by
      rw [toReal_maximum, toReal_one]; exact le_max_left _ _
    have hmk : toReal (maximum one (nsmulDown P.k (one : 𝕋))) ≤ (P.k : ℝ) := by
      rw [toReal_maximum, toReal_one]; exact max_le hk1 hD
    have hD0 : (0 : ℝ) < toReal (maximum one (nsmulDown P.k (one : 𝕋))) := by linarith
    have hU0 : (0 : ℝ) < toReal (nsmulUp P.k (one : 𝕋)) := by linarith
    intro i
    -- the coordinate of the mean is the coordinate sum over the count
    have hc : (InflatedContSet.nominal P).center i = (∑ l, toReal (P.V l i)) / P.k := by
      rw [VPolytope.nominal_eq]
      simp [Real.VPolytope.center, Finset.sum_apply, div_eq_inv_mul]
    refine ⟨?_, ?_⟩
    · change toReal (minimum _ _) ≤ (InflatedContSet.nominal P).center i
      rw [hc, toReal_minimum]
      refine le_trans (min_le_min (divDown_le_div _ _ hU0) (divDown_le_div _ _ hD0)) ?_
      exact VPolytope.aux_div_ge (sumDown_le_sum _) hD0 hmk hU
    · change (InflatedContSet.nominal P).center i ≤ toReal (maximum _ _)
      rw [hc, toReal_maximum]
      refine le_trans ?_ (max_le_max (div_le_divUp _ _ hU0) (div_le_divUp _ _ hD0))
      exact VPolytope.aux_div_le (sum_le_sumUp _) hD0 hmk hU
  · -- the mean is a point of the nominal polytope, and the error box is added to it
    rintro _ ⟨x, hx, e, he, rfl⟩
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨_, Real.VPolytope.center_mem _ hk, e, he, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
