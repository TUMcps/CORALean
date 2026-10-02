import CORALean.ContSet.Taylm.Real.Operations.Mtimes
import CORALean.ContSet.Taylm.Real.Theorems.SumOuter
import CORALean.ContSet.Taylm.Real.Theorems.SmulOuter

/-!
# `Taylm.mtimes` encloses the matrix image

Row `i` encloses `Σⱼ M i j fⱼ`, the image of the enclosed functions under `M`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.mtimes_outer {k m : ℕ} (M : Mat ℝ k m) {T : Fin m → Taylm n}
    {f : Fin m → Vec ℝ n → ℝ} (h : ∀ j, (T j).Encloses (f j)) (i : Fin k) :
    (Taylm.mtimes M T i).Encloses fun t => ∑ j, M i j * f j t :=
  Taylm.sum_outer fun j => Taylm.smul_outer (M i j) (h j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
