module

public import CORALean.Specification.STL.Operations.DepReachFloat
public import CORALean.Specification.STL.Theorems.DepReachAtFloatOuter
public import CORALean.Specification.STL.Theorems.DepReachConstsFloatOuter
public import CORALean.Specification.STL.Theorems.DepReachIntervalFloatOuter

@[expose] public section

/-!
# The float reachable set over a time interval encloses the exact one

Over [1, Alg. 1], the float constants enclose the real ones (`depReachConstsFloat_outer`), the float
states after `i` and `i + 1` steps enclose the real ones (`depReachAtFloat_outer`), and the interval
set follows (`depReachIntervalFloat_outer`). It holds the exact `conv(H(t_i), H(t_{i+1})) ⊕
P(t_{i+1}) ⊕ C_i` with `C_i` the exact products mapped `i` times by `e^{AΔt}`; neither the real
`linComb` nor the real `C_i` can be compared, as `depReachIntervalFloat_outer` and
`depReachInitFloat_outer` explain.
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
* the exact reachable set over the interval lies inside the float one
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

open Pointwise Matrix NormedSpace Float Float.FloatOps Float.SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float `R(τ_i)` holds the exact reachable set over the interval. -/
theorem STL.depReachFloat_interval_outer (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) {Δt : 𝕋}
    (hr : 0 ≤ toReal Δt) {κ η : ℕ}
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((κ : ℝ) + 2) ≤ 1 / 2)
    (hε' : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((η : ℝ) + 2) ≤ 1 / 2) {X₀r : Real.Zonotope (Vec ℝ n)} {X₀f : Float.Zonotope (Vec 𝕋 n)}
    {Ur : Real.Zonotope (Vec ℝ m)} {Uf : Float.Zonotope (Vec 𝕋 m)} (hc : Ur.c = toRealVec Uf.c)
    (hU : Ur.construct ⊆ Uf.construct) (hX : X₀r.construct ⊆ X₀f.construct)
    (i : ℕ) : -- --- CONCL ---
    let csR := STL.depReachConsts (toRealMat A) (toRealMat B) Ur (toReal Δt) κ
    let sR := STL.depReachAt (toRealMat A) (toReal Δt) csR X₀r i
    let sR' := STL.depReachAt (toRealMat A) (toReal Δt) csR X₀r (i + 1)
    (convexHull ℝ (sR.H.construct ∪ sR'.H.construct) + (sR'.Pc.construct + sR'.D.construct)) +
      (exp (toReal Δt • toRealMat A) *ᵥ ·)^[i] ''
        {y | ∃ M ∈ csR.F.construct, ∃ x ∈ X₀r.construct, ∃ M' ∈ csR.G.construct,
          y = M *ᵥ x + M' *ᵥ csR.ũ} ⊆
      (STL.depReachFloat A B X₀f Uf Δt κ η i).2.construct := by -- --- PROOF ---
  intro csR sR sR'
  have hcs := STL.depReachConstsFloat_outer A B hr κ hε hc hU
  exact STL.depReachIntervalFloat_outer (STL.depReachAtFloat_outer A Δt hε' hX hcs i)
    (STL.depReachAtFloat_outer A Δt hε' hX hcs (i + 1))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
