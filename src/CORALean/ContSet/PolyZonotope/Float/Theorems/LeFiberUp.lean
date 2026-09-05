import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Float.Theorems.SumMask

/-!
# The upward masked sum never undershoots the exact fibre sum
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}

theorem PolyZonotope.le_fiberUp (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n)
    (j : Fin h) :
    Real.PolyZonotope.fiberSum r (fun l => toReal (G i l)) j
      ≤ toReal (PolyZonotope.fiberUp r G i j) := by
  rw [← PolyZonotope.sum_mask r G i j]
  exact sum_le_sumUp _

end CORALean.Float
