import CORALean.Global.Mathlib

/-!
# The exponential series without its constant order

Orders `1` through `η` of `e^c`, bounded by `e^c - 1` — the whole series minus
the order the partial sums always carry. It is the finite counterpart of
`tsum_le_expTail`: that one bounds what truncation leaves out, this one bounds
what it keeps beyond the constant term.

A Minkowski sum over the orders of an input solution is what asks for it. Each
order is free to pick its own input where a trajectory holds one, and orders `1`
upwards are exactly the ones that difference does not cancel at.

Scalar, so a caller at matrices supplies `c = ‖r A‖` and the matrix norm
instances stay out of the elaboration.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every order but the constant one, summed and bounded. -/
theorem sum_expTail_le {c : ℝ} (hc : 0 ≤ c) (η : ℕ) :
    ∑ i ∈ Finset.range η, ((Nat.factorial (i + 1) : ℝ)⁻¹ * c ^ (i + 1))
      ≤ Real.exp c - 1 := by -- --- PROOF ---
  have hkey := Real.sum_le_exp_of_nonneg hc (η + 1)
  -- the partial sum, split at the constant order the bound has to give back
  have hsplit : ∑ i ∈ Finset.range (η + 1), c ^ i / (Nat.factorial i : ℝ)
      = (∑ i ∈ Finset.range η, c ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) + 1 := by
    rw [Finset.sum_range_succ' (fun i => c ^ i / (Nat.factorial i : ℝ)) η]
    norm_num
  have hterm : ∑ i ∈ Finset.range η, ((Nat.factorial (i + 1) : ℝ)⁻¹ * c ^ (i + 1))
      = ∑ i ∈ Finset.range η, c ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) :=
    Finset.sum_congr rfl fun i _ => by rw [div_eq_inv_mul]
  rw [hterm]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
