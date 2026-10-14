module

public import CORALean.ContSet.Taylm.Real.Operations.Exp
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorScaled
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# `Taylm.exp` keeps the `(n+1)`-st order scaling

[1, Thm. 1], eq. (2.9), at the source's first intrinsic ([1, Def. 3 (exp)]). `taylor_scaled`
asks for a bound on the coefficients and one on the derivative bound; for `exp` both come from
the scaling itself: the centre is at most `C`, so each `exp(c)/k!` is at most `exp C`, and the
top of the range is within `2C·h ≤ 2C` of the centre, so `D ≤ exp (3C)`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.exp_scaled {T : Taylm n} {h C : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (hT : T.Scaled h C) :
    T.exp.Scaled h (Real.exp C * ∑ k : Fin (T.maxOrder + 1), (8 * C) ^ (k : ℕ)
      + Real.exp (3 * C) * (2 * C) ^ (T.maxOrder + 1)) := by -- --- PROOF ---
  have hc := Taylm.abs_constCoef_le T h0
  have hC : |T.constCoef| ≤ C := le_trans hc hT.1
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) hC
  -- the coefficients: `exp c / k! ≤ exp c ≤ exp C`
  refine Taylm.taylor_scaled h0 h1 hT (fun k _ => ?_) ?_
  · rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, abs_div, abs_of_pos (Real.exp_pos _),
      Nat.abs_cast]
    have hf : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos _
    refine le_trans (div_le_self (Real.exp_pos _).le hf) ?_
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) hC)
  -- the derivative bound: the top of the range is within `2C·h` of the centre
  · have hr := Taylm.reach_le h0 h1 hT
    have htop : T.bounds.sup - T.constCoef ≤ 2 * C * h :=
      le_trans (le_trans (le_abs_self _) (le_max_right _ _)) hr
    rw [abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 (max_le (by linarith [le_abs_self T.constCoef]) ?_)
    nlinarith [le_abs_self T.constCoef]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
