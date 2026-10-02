import CORALean.ContSet.Capsule.Real.Capsule
import Mathlib.Data.Matrix.Mul

/-!
# CORA's `capsule/mtimes` radius, as printed

Centre and generator mapped, radius `r · lam`, with `lam` the largest eigenvalue of `M Mᵀ`. Kept
only so that `Capsule.mtimes_cora_counterexample` can state that it is unsound; `Capsule.mtimes`
is the sound operation.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `mtimes` as printed: radius `r · lam`, with `lam` the largest eigenvalue of `M Mᵀ`. -/
def Capsule.mtimesCora (M : Mat ℝ m n) (C : Capsule n) (lam : ℝ) : Capsule m :=
  ⟨M.mulVec C.c, M.mulVec C.g, C.r * lam⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
