import CORALean.ContSet.Taylm.Real.Operations.Sin
import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.sin` encloses `sin ∘ f`

Every derivative of `sin` is bounded by one.

[1, Def. 3 (sin)]: the result is a Taylor model of `sin ∘ f`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sin_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.sin.Encloses fun t => Real.sin (f t) := by
  refine Taylm.taylor_outer h _ _ _ (fun ξ _ => Real.contDiff_sin.contDiffAt) fun ξ _ => ?_
  exact abs_iteratedDeriv_sin_le _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
