module

public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `rowLin`, over a floating-point scalar

Row `i` of a float matrix, as the functional over ℝ that it denotes: the direction `boundDot`
and `FloatBound` take when it is a matrix row.

It is only a name for `Real.HPolytope.rowLin (toRealMat M) i`, kept because the statements that
take a row as the direction of a `FloatBound` use it at every site and would otherwise spell the
conversion out each time.

## Inputs
* `M` – `q × n` matrix
* `i` – index below `q`

## Output
* row `i` of a float matrix as a functional over ℝ, `Real.HPolytope.rowLin (toRealMat M) i`
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

/-- Row `i` of a float matrix as a functional over ℝ, `Real.HPolytope.rowLin (toRealMat M) i`. -/
abbrev rowLin (M : Mat 𝕋 q n) (i : Fin q) : Vec ℝ n →ₗ[ℝ] ℝ :=
  Real.HPolytope.rowLin (toRealMat M) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
