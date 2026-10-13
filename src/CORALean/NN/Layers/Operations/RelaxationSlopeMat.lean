module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.NN.Layers.Definitions.Relaxation

@[expose] public section

/-!
# The affine part of a relaxation, as a matrix

The slopes the relaxation chose, one per neuron, on a diagonal: propagating the set through it
with `mtimes` keeps the neurons' dependence on the input, and only the leftover deviation is
thrown into a box. Taking every slope `0` is legal, and is exactly where that dependence is
lost. `diagonalBlock` only places the stored slopes, so the matrix is exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The affine map the relaxation chose, as a matrix, so that `mtimes` carries it. -/
def Relaxation.slopeMat (R : Relaxation 𝕋) (I : Interval (Vec 𝕋 n)) : Mat 𝕋 n n :=
  diagonalBlock fun i => R.slope (I.inf i) (I.sup i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
