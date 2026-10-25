module

public import CORALean.ContSet.Taylm.Real.Operations.Basic

@[expose] public section

/-!
# The terms of degree two and more

The nonlinear part of a term list, whose bound is `Iₕ` in [1, Sec. 2].

## Inputs
* `L` – terms of the polynomial

## Output
* the terms of degree two and more

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range Bounders".
      2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.higherTerms (L : List (ℝ × (Fin n → ℕ))) : List (ℝ × (Fin n → ℕ)) :=
  L.filter fun a => decide (2 ≤ Taylm.degree a.2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
