module

public import CORALean.ContSet.Taylm.Real.Operations.Sinh
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
public import CORALean.ContSet.Taylm.Real.Theorems.AbsLeMag
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.sinh` encloses `sinh ∘ f`

The magnitude bounds the hull, and `cosh` is monotone in `|x|`.

[1, Def. 3 (sinh)]: the result is a Taylor model of `sinh ∘ f`.

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

theorem Taylm.sinh_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.sinh.Encloses fun t => Real.sinh (f t) := by
  refine Taylm.taylor_outer h _ _ _ (fun ξ _ => Real.contDiff_sinh.contDiffAt) fun ξ hξ => ?_
  exact abs_iteratedDeriv_sinh_le _ (T.abs_le_mag hξ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
