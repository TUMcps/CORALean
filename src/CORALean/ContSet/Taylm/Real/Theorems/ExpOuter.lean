import CORALean.ContSet.Taylm.Real.Operations.Exp
import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# `Taylm.exp` encloses `exp ∘ f`

[1, Def. 3 (exp)]: the result is a Taylor model of `exp ∘ f`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.exp_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.exp.Encloses fun t => Real.exp (f t) := by
  refine Taylm.taylor_outer h _ _ _ (fun ξ _ => Real.contDiff_exp.contDiffAt) fun ξ hξ => ?_
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 hξ.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
