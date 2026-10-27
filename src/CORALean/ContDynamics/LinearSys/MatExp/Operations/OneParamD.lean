module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `MatExp.oneParamD`

The auxiliary matrices `D_i` of [1, Thm. 1]: `D_0 = I`, `D_i = D_{i-1} C`, so `D_i = Cⁱ`, the
part of `(C + βG)ⁱ` free of the parameter `β`.

## Inputs
* `C` – matrix

## Output
* power of the matrix by index

## References

* [1] [M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". 2012 American Control Conference (ACC),
      2012.](../../../../../../references/2012/althoff-acc-low-order-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.oneParamD (C : Mat ℝ n n) : ℕ → Mat ℝ n n
  | 0 => 1  -- `D_0 = I`
  | i + 1 => MatExp.oneParamD C i * C  -- `D_i = D_{i-1} C`

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
