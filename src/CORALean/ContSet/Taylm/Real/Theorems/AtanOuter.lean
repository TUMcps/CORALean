import CORALean.ContSet.Taylm.Real.Operations.Atan
import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
import CORALean.ContSet.Taylm.Real.Theorems.AbsLeMag
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.atan` encloses `atan ∘ f`

No domain condition: `atan` is smooth on `ℝ`.

[1, Def. 3 (arctan)]: a Taylor model of `arctan ∘ f`, with no condition on the range.

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

theorem Taylm.atan_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.atan.Encloses fun t => Real.arctan (f t) := by
  refine Taylm.taylor_outer h _ _ _ (fun ξ _ => Real.contDiff_arctan.contDiffAt) fun ξ hξ => ?_
  exact abs_iteratedDeriv_atan_le _ (T.abs_le_mag hξ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
