module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The selection matrix of a NARX window

`E = [0 I]` of [1, Cor. 2]: it reads the last block of the window `(y_{k-n_p}, …, y_{k-1})`,
and `Eᵀ` writes a vector into that block.

## Inputs
* `np` – number of lags
* `ny` – output dimension

## Output
* the matrix selecting the last block of the window

## References

* [1] [L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE Transactions on
      Automatic Control,
      2026.](../../../../../references/2026/luetzow-tac-reachset-conformant-identification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Cor. 2]: `E = [0_{ny × (np-1)ny}  I_{ny}]`. -/
def Conform.narxE (np ny : ℕ) : Mat ℝ ny (np * ny) :=
  Matrix.of fun r c =>
    if (finProdFinEquiv.symm c).1.val + 1 = np ∧ (finProdFinEquiv.symm c).2 = r then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
