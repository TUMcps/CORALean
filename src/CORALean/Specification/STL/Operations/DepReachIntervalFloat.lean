module

public import CORALean.ContSet.Zonotope.Float.Operations.LinComb
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.Specification.STL.Definitions.DepReachStateFloat
public import CORALean.Specification.STL.Operations.DepReachInterval

@[expose] public section

/-!
# The time interval reachable set of the dependency preserving reachability algorithm, over floats

[1, Eq. 14-20] and line 9 of [1, Alg. 1]: `R(τ_i) = conv(H(t_i), H(t_{i+1})) ⊕ P(t_{i+1}) ⊕ C_i`,
the convex hull enclosed by Eq. (8), `Zonotope.linComb`, whose generators are `½(G₁+G₂)`,
`½(G₁-G₂)` and `½(c₁-c₂)`, with the bounds held in `𝕋` and the rounding paid into the error box. It
takes the states at `t_i` and `t_{i+1}`. Soundness is `STL.depReachIntervalFloat_outer`.

## Inputs
* `s` – float state at the step start
* `s'` – float state at the step end

## Output
* the reachable set over the time interval of the step
## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
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

/-- [1, Eq. 14-20]: `R(τ_i) = conv(H(t_i), H(t_{i+1})) ⊕ P(t_{i+1}) ⊕ C_i`, rounded outward. -/
def STL.depReachIntervalFloat (s s' : STL.DepReachStateFloat 𝕋 n) : Float.Zonotope (Vec 𝕋 n) :=
  ((s.H.linComb s'.H).plus (s'.Pc.plus s'.D)).plus s.C

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
