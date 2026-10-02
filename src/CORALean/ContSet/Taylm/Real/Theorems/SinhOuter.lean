import CORALean.ContSet.Taylm.Real.Operations.Sinh
import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
import CORALean.ContSet.Taylm.Real.Theorems.AbsLeMag
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.sinh` encloses `sinh ∘ f`

The magnitude bounds the hull, and `cosh` is monotone in `|x|`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


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
