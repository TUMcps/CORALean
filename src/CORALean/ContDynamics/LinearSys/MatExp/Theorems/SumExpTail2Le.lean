import Mathlib.Analysis.Complex.Exponential

/-!
# The exponential series without its first two orders

Orders `2` through `η + 1` of `e^c`, bounded by `e^c - 1 - c`. It is
`sum_expTail_le` one order further along, and the index is where the
interpolation error starts: the constant and linear terms of a straight line
between the ends of a step cancel, so `correctionMatrix` is indexed from `2`.

Bounding the finite part this way is what makes the correction second order in
the step — `e^c - 1 - c` is `O(c²)` — where the hull it corrects is only first
order.

Scalar, so a caller at matrices supplies `c = ‖r A‖` and the matrix norm
instances stay out of the elaboration.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every order from the second on, summed and bounded. -/
theorem sum_expTail2_le {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    ∑ i ∈ Finset.range m, ((Nat.factorial (i + 2) : ℝ)⁻¹ * c ^ (i + 2))
      ≤ Real.exp c - 1 - c := by -- --- PROOF ---
  have hkey := Real.sum_le_exp_of_nonneg hc (m + 2)
  -- the partial sum, split at the two orders the bound has to give back
  have h1 : ∑ i ∈ Finset.range (m + 2), c ^ i / (Nat.factorial i : ℝ)
      = (∑ i ∈ Finset.range (m + 1), c ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) + 1 := by
    rw [Finset.sum_range_succ' (fun i => c ^ i / (Nat.factorial i : ℝ)) (m + 1)]
    norm_num
  have h2 : ∑ i ∈ Finset.range (m + 1), c ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)
      = (∑ i ∈ Finset.range m, c ^ (i + 2) / (Nat.factorial (i + 2) : ℝ)) + c := by
    rw [Finset.sum_range_succ' (fun i => c ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) m]
    norm_num
  have hterm : ∑ i ∈ Finset.range m, ((Nat.factorial (i + 2) : ℝ)⁻¹ * c ^ (i + 2))
      = ∑ i ∈ Finset.range m, c ^ (i + 2) / (Nat.factorial (i + 2) : ℝ) :=
    Finset.sum_congr rfl fun i _ => by rw [div_eq_inv_mul]
  rw [hterm]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
