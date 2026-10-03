import CORALean.ContSet.Taylm.Real.Operations.QuadTerms

/-!
# `Q_{x₀}` as a Taylor model

[1, Sec. 3]'s `Q_{x₀} = ½ (x - x₀)ᵗ H (x - x₀)`, exactly, with no remainder.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.quadForm (H : Mat ℝ n n) (x0 : Vec ℝ n) (N : ℕ) : Taylm n :=
  ⟨Taylm.quadTerms H x0, 0, 0, N⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
