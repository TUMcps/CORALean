import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# State-dependent constant flow

[1, Eq. 3]: the solution `y(t) = y₀ + (Ay₀ + b)t` of eq. (2), `ẏ = Ay₀ + b` — a constant
flow for each initial state, but one that depends on it, which is what lets [1] write the
guard hit as a function of `y₀`. `hasDerivAt_sdcFlow` is that it solves (2).

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 3]: `y(t) = y₀ + (Ay₀ + b)t`. -/
def GuardMap.sdcFlow (A : Mat ℝ n n) (b y₀ : Vec ℝ n) (t : ℝ) : Vec ℝ n :=
  y₀ + t • (A *ᵥ y₀ + b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
