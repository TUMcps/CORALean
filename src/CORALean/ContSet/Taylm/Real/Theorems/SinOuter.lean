import CORALean.ContSet.Taylm.Real.Operations.Sin
import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.sin` encloses `sin ∘ f`

Every derivative of `sin` is bounded by one.
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
