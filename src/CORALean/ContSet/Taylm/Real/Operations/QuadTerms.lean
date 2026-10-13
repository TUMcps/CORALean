module

public import CORALean.ContSet.Taylm.Real.Taylm
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `½ (t - x₀)ᵀ H (t - x₀)` as a term list

The `Q_{x₀}` of the quadratic fast bounder, [1, Sec. 3]: the quadratic, linear and constant terms
of the form, `H` in any (not necessarily symmetric) matrix.

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

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Matrix
noncomputable def Taylm.quadTerms (H : Mat ℝ n n) (x0 : Vec ℝ n) : List (ℝ × (Fin n → ℕ)) :=
  (List.ofFn fun i => List.ofFn fun j => (H i j / 2, Pi.single i 1 + Pi.single j 1)).flatten ++
    (List.ofFn fun i => (-((H *ᵥ x0) i + (Hᵀ *ᵥ x0) i) / 2, Pi.single i 1)) ++
    [(x0 ⬝ᵥ (H *ᵥ x0) / 2, 0)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
