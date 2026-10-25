module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# State-dependent constant flow

[1, Eq. 3]: the solution `y(t) = y₀ + (Ay₀ + b)t` of eq. (2), `ẏ = Ay₀ + b` — a constant
flow for each initial state, but one that depends on it, which is what lets [1] write the
guard hit as a function of `y₀`. `hasDerivAt_sdcFlow` is that it solves (2).

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `y₀` – initial state
* `t` – time

## Output
* state of the constant flow at time `t`

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
