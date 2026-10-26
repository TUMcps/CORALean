module

public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Specification.STL.Definitions.DepReachState

@[expose] public section

/-!
# The state of the loop of the dependency preserving reachability algorithm, over floats

[1, Alg. 1]: what the loop carries from `t_i` to `t_{i+1}`, held in float zonotopes: `H(t_i)`,
`P_c(t_i)`, `D_i` and `C_i`. A float state encloses a real one when each of its zonotopes holds
the points of the real zonotope in its place (`DepReachStateFloat.Encloses`), which is how the
rounded loop is related to the exact one: the points of the real sets stay in the float ones. The
curvature set `C_i` is held against a set `E` of points instead of the real zonotope `C_i`: the
real `C₀` is the box of a conservative zonotope product (`Zonotope.mtimesIntervalMat`) whose
overshoot the rounded product does not reproduce, so only the exact points are held.

## Inputs
* `𝕋` – scalar of the stored floats
* `n` – state dimension

## Output
* the state of the loop in floats
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

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- `H(t_i)`, `P_c(t_i)`, `D_i` and `C_i` of [1, Alg. 1], as float zonotopes. -/
structure STL.DepReachStateFloat (𝕋 : Type) (n : ℕ) where
  H : Float.Zonotope (Vec 𝕋 n)
  Pc : Float.Zonotope (Vec 𝕋 n)
  D : Float.Zonotope (Vec 𝕋 n)
  C : Float.Zonotope (Vec 𝕋 n)

/-- The float state holds the points of `H`, `P_c` and `D` of the real state and the set `E`. -/
def STL.DepReachStateFloat.Encloses (sF : STL.DepReachStateFloat 𝕋 n) (sR : STL.DepReachState n)
    (E : Set (Vec ℝ n)) : Prop :=
  sR.H.construct ⊆ sF.H.construct ∧ sR.Pc.construct ⊆ sF.Pc.construct ∧
    sR.D.construct ⊆ sF.D.construct ∧ E ⊆ sF.C.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
