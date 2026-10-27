module

public import CORALean.Specification.STL.Operations.DepReachFloat
public import CORALean.Specification.STL.Theorems.DepReachAtFloatOuter
public import CORALean.Specification.STL.Theorems.DepReachConstsFloatOuter
public import CORALean.Specification.STL.Theorems.DepReachPointFloatOuter

@[expose] public section

/-!
# The float reachable set at a time point encloses the real one

Over [1, Alg. 1], the float constants enclose the real ones (`depReachConstsFloat_outer`), the float
state after `i` steps encloses the real one (`depReachAtFloat_outer`), and the point set follows
(`depReachPointFloat_outer`).
## Inputs
* `A` – float dynamics matrix
* `B` – float input matrix
* `Δt` – float time step
* `κ` – Taylor order
* `η` – Taylor order of the matrix exponential
* `X₀r` – real initial set
* `X₀f` – float initial set
* `Ur` – real input set
* `Uf` – float input set
* `i` – step index

## Hypotheses
* `hr` – the time step is nonnegative
* `hε` – the float norm bound is small enough for the order of the constants
* `hε'` – the float norm bound is small enough for the order of the exponential
* `hc` – the real and float input sets have the same center
* `hU` – the real input set lies inside the float one
* `hX` – the real initial set lies inside the float one

## Conclusion
* the real reachable set at the time point lies inside the float one
## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float `R(t_i)` holds the real `R(t_i)`. -/
theorem STL.depReachFloat_point_outer (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) {Δt : 𝕋}
    (hr : 0 ≤ toReal Δt) {κ η : ℕ}
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((κ : ℝ) + 2) ≤ 1 / 2)
    (hε' : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((η : ℝ) + 2) ≤ 1 / 2) {X₀r : Real.Zonotope (Vec ℝ n)} {X₀f : Float.Zonotope (Vec 𝕋 n)}
    {Ur : Real.Zonotope (Vec ℝ m)} {Uf : Float.Zonotope (Vec 𝕋 m)} (hc : Ur.c = toRealVec Uf.c)
    (hU : Ur.construct ⊆ Uf.construct) (hX : X₀r.construct ⊆ X₀f.construct)
    (i : ℕ) : -- --- CONCL ---
    (STL.depReach (toRealMat A) (toRealMat B) X₀r Ur (toReal Δt) κ i).1.construct ⊆
      (STL.depReachFloat A B X₀f Uf Δt κ η i).1.construct := by -- --- PROOF ---
  exact STL.depReachPointFloat_outer
    (STL.depReachAtFloat_outer A Δt hε' hX (STL.depReachConstsFloat_outer A B hr κ hε hc hU) i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
