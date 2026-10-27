module

public import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT

@[expose] public section

/-!
# The extended output matrix

`Ā_ext` of [1, Thm. 1], (10): identity blocks above the diagonal, then the last block row
`Ā_p … Ā_1`. It is the state matrix of the conversion to `LinearSysDT`, read into ℝ, so
the window recursion (11) is `toLinearSysDT_step` and needs no second proof.

## Inputs
* `sys` – ARX system

## Output
* the extended output matrix

## References

* [1] [L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.](../../../../../references/2023/luetzow-cdc-armax.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.Aext (sys : LinearARX 𝕋 dy du p) : Mat ℝ (p * dy) (p * dy) :=
  toRealMat sys.toLinearSysDT.A

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
