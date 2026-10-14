module

public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `rowLin`, over a floating-point scalar

Row `i` of a float matrix, as the functional over ℝ that it denotes. Every
bound in this layer is stated against one of these.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` of a float matrix, as the functional over ℝ that it denotes. Every
bound below is stated against one of these. -/
abbrev rowLin (M : Mat 𝕋 q n) (i : Fin q) : Vec ℝ n →ₗ[ℝ] ℝ :=
  Real.HPolytope.rowLin (toRealMat M) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
