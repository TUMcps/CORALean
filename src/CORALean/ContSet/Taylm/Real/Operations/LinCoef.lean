module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# The linear coefficients of a term list

`Lₖ`, the sum of the coefficients of `tₖ` alone: the linear part that the linear dominated bounder
of [1, Sec. 2] follows.

## Inputs
* `L` – terms of the polynomial
* `k` – variable index

## Output
* sum of the coefficients of that variable alone

## References

* [1] [K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range Bounders".
      2005.](../../../../../../references/2005/makino-tc-global-optimization.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.linCoef (L : List (ℝ × (Fin n → ℕ))) (k : Fin n) : ℝ :=
  ((L.filter fun a => decide (a.2 = Pi.single k 1)).map Prod.fst).sum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
