module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.EuclideanNorm

@[expose] public section

/-!
# `Interval.normSq` over floats

CORA's `norm_` at `type = 2`, as the squared length rounded up. There is no float square root, so
the root is a certificate (`Global/Float/EuclideanNorm`): the caller proposes `σ` and
`normSq ≤ σ·σ` is the check, in `Theorems/NormNominalLe`.

## Inputs
* `I` – interval box

## Output
* squared Euclidean length of the box, rounded up
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The squared Euclidean norm of `normMag`, rounded up. -/
def Interval.normSq (I : Interval (Vec 𝕋 n)) : 𝕋 := sqSumUp I.normMag

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
