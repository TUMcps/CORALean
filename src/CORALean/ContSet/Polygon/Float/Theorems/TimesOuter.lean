import CORALean.ContSet.Polygon.Float.Operations.Times
import CORALean.ContSet.Polygon.Float.Theorems.MtimesOuter

/-!
# `Polygon.times` encloses the image

`mtimes_outer` at the diagonal matrix, which reads as `Matrix.diagonal` over the reals
(`toReal_diagonalBlock`).
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.times_outer (v : Vec 𝕋 2) (P : Polygon 𝕋) :
    (diagonal (toRealVec v) *ᵥ ·) '' ContSet.construct P ⊆
      ContSet.construct (Polygon.times v P) := by
  have h : toRealMat (diagonalBlock v) = diagonal (toRealVec v) :=
    funext fun i => funext fun l => toReal_diagonalBlock v i l
  have := Polygon.mtimes_outer (diagonalBlock v) P
  rwa [h] at this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
