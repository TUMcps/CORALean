import CORALean.ContSet.Taylm.Real.Operations.QuadForm
import CORALean.ContSet.Taylm.Real.Operations.Minus
import CORALean.ContSet.Taylm.Real.Operations.Bounds

/-!
# The quadratic fast bounder

[1, Sec. 3]: `l(P + I) = l(P - Q_{x₀}) + l(Q_{x₀}) + l(I)` with `l(Q_{x₀}) = 0` for a positive
semidefinite `H`; `l(P - Q_{x₀}) + l(I)` is the lower bound of the model `T - Q_{x₀}`.

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

noncomputable def Taylm.qfbLower (T : Taylm n) (H : Mat ℝ n n) (x0 : Vec ℝ n) : ℝ :=
  (T.minus (Taylm.quadForm H x0 T.maxOrder)).bounds.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
