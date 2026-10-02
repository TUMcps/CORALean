import CORALean.ContSet.Taylm.Real.Operations.Tanh
import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
import CORALean.ContSet.Taylm.Real.Theorems.AbsLeMag
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.tanh` encloses `tanh ∘ f`

`tanh` is smooth and `|tanh| ≤ 1`, so `abs_iteratedDeriv_tanh_le` applies on all of `ℝ`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.tanh_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.tanh.Encloses fun t => Real.tanh (f t) := by
  refine Taylm.taylor_outer h _ _ _ (fun ξ _ => contDiff_tanh.contDiffAt) fun ξ _ =>
    abs_iteratedDeriv_tanh_le _ ξ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
