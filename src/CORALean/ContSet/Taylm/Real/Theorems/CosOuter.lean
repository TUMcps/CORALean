import CORALean.ContSet.Taylm.Real.Operations.Cos
import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.cos` encloses `cos ∘ f`

Every derivative of `cos` is bounded by one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.cos_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.cos.Encloses fun t => Real.cos (f t) := by
  refine Taylm.taylor_outer h _ _ _ (fun ξ _ => Real.contDiff_cos.contDiffAt) fun ξ _ => ?_
  exact abs_iteratedDeriv_cos_le _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
