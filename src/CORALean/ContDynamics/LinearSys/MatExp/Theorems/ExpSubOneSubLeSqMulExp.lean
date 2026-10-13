module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpTail2

@[expose] public section

/-!
# `e^x - 1 - x ≤ x²/2 · e^x` for `x ≥ 0`

The second-order remainder of the exponential, by its Lagrange form's largest value. Term
by term: `x^{i+2}/(i+2)! ≤ x²/2 · x^i/i!`, since `(i+2)! ≥ 2·i!`.

This is the step [1]'s proofs of Lemma 2 and Theorem 1 need when they bound
`α_r = (e^{r‖A‖} - 1 - r‖A‖) sup ‖x‖` by a multiple of `r‖A‖ e^{r‖A‖}`: the factor it
gives is `(r‖A‖)²`, not the `r²` the printed proof of [1, Lemma 2] uses.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exponential's second-order remainder, at most `x²/2` times the exponential. -/
theorem exp_sub_one_sub_le_sq_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 * Real.exp x := by -- --- PROOF ---
  have h : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  refine hasSum_le (fun i => ?_) (hasSum_exp_tail2 x) (h.mul_left (x ^ 2 / 2))
  -- `(i+2)! ≥ 2·i!`, which is the whole comparison
  have hf : (2 * i.factorial : ℝ) ≤ ((i + 2).factorial : ℝ) := by
    have : 2 * i.factorial ≤ (i + 2).factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
      exact Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))
    exact_mod_cast this
  have hpos : (0 : ℝ) < i.factorial := by exact_mod_cast Nat.factorial_pos i
  have hp : 0 ≤ x ^ i := pow_nonneg hx _
  rw [div_le_iff₀ (by positivity), pow_add]
  calc x ^ i * x ^ 2 = x ^ 2 / 2 * (x ^ i / i.factorial) * (2 * i.factorial) := by
        field_simp
    _ ≤ x ^ 2 / 2 * (x ^ i / i.factorial) * ((i + 2).factorial) := by
        gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
