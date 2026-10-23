module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# The Hessian of a term list

At `0`: twice the coefficient of `xₖ²` on the diagonal, the coefficient of `xₖxₗ` off it, as
CORA's `optLinQuad` reads it. The `H` of [1, Sec. 3].

## Inputs
* `L` – terms of the polynomial

## Output
* Hessian matrix of the terms at zero

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.hessian (L : List (ℝ × (Fin n → ℕ))) : Mat ℝ n n := fun k l =>
  ((L.filter fun a => decide (a.2 = Pi.single k 1 + Pi.single l 1)).map Prod.fst).sum *
    (if k = l then 2 else 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
