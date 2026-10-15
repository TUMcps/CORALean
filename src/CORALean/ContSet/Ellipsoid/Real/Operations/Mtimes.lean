module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.mtimes`

CORA's `@ellipsoid/mtimes` with a matrix factor: `Q ↦ M Q Mᵀ` and `q ↦ M q`, exact. CORA then
symmetrises, `1/2 (M + M')`, against rounding; in exact arithmetic `M Q Mᵀ` is symmetric already,
so that step is the identity here. The dimension may change: `M` is `m × n`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.mtimes (M : Mat ℝ m n) (E : Ellipsoid n) : Ellipsoid m where
  Q := M * E.Q * Mᵀ
  q := M *ᵥ E.q
  psd := by simpa [conjTranspose_eq_transpose_of_trivial] using E.psd.mul_mul_conjTranspose_same M

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
