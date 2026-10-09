import CORALean.ContSet.SpectraShadow.Real.Operations.ArrowMat

/-!
# The arrowhead matrix is symmetric

`arrowMat s t w` has `w` in its first row and first column alike, so it is Hermitian.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem arrowMat_isHermitian (s t : ℝ) (w : Vec ℝ N) : (arrowMat s t w).IsHermitian := by
  -- each of the four cases of an entry
  ext p q
  refine Fin.cases ?_ (fun i => ?_) p <;> refine Fin.cases ?_ (fun j => ?_) q <;>
    simp [arrowMat, conjTranspose_apply, eq_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
