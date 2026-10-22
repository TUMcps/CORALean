module

public import CORALean.ContDynamics.LinearARX.LinearARX
public import CORALean.Global.Interfaces
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContDynamics.OutputEq.OutputEq

@[expose] public section

/-!
# The output equation of the converted system

`y(k)` is block `0` of the window `stack y k`: `C` picks it, and `D = 0`, the input
being already in the state's next window, and `k = 0`.

## Inputs
* `_sys` – ARX system

## Output
* the output equation picking the first block
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.outputEq (_sys : LinearARX 𝕋 dy du p) : OutputEq 𝕋 (p * dy) (p * dy) dy where
  C := Matrix.of fun r c =>
    if (finProdFinEquiv.symm c).1.val = 0 ∧ (finProdFinEquiv.symm c).2 = r then 1 else 0
  D := 0
  k := 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
