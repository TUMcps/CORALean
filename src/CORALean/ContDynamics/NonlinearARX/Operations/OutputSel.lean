module

public import CORALean.ContDynamics.NonlinearARX.NonlinearARX
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# Reading the output off the window

`y(k)` is block `0` of the window at step `k`; `outputSel` is the matrix that selects
it, as `LinearARX.outputEq`'s `C`, over `ℝ`.

## Inputs
* `_sys` – ARX system

## Output
* the matrix selecting the first output block of the window
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p : ℕ} {𝕋 : Type} [CORALean.Float.FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearARX.outputSel (_sys : NonlinearARX dy du p) : Mat 𝕋 dy (p * dy) :=
  Matrix.of fun r c =>
    if (finProdFinEquiv.symm c).1.val = 0 ∧ (finProdFinEquiv.symm c).2 = r then
      CORALean.Float.FloatOps.one
    else CORALean.Float.FloatOps.zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
