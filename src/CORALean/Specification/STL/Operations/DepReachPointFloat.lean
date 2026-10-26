module

public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.Specification.STL.Definitions.DepReachStateFloat
public import CORALean.Specification.STL.Operations.DepReachPoint

@[expose] public section

/-!
# The time point reachable set of the dependency preserving reachability algorithm, over floats

[1, Eq. 14-20] and line 8 of [1, Alg. 1]: `R(t_i) = H(t_i) ⊕ P(t_i)`, `P(t_i) = P_c(t_i) ⊕ D_i`, as
float zonotopes: the generators of `H(t_i)`, then those of `P_c(t_i)`, then those of `D_i`, the
rounding of the centers paid into the error box. Soundness is `STL.depReachPointFloat_outer`.

## Inputs
* `s` – float algorithm state

## Output
* the reachable set at the time point
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 14-20]: `R(t_i) = H(t_i) ⊕ P(t_i)`, rounded outward. -/
def STL.depReachPointFloat (s : STL.DepReachStateFloat 𝕋 n) : Float.Zonotope (Vec 𝕋 n) :=
  s.H.plus (s.Pc.plus s.D)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
