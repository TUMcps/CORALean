module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# The bloating `D`

[1, Eq. 14-20]: `D = (Σ_{j=1}^κ A^j Δt^{j+1}/(j+1)!) U₀ ⊕ ⨁_{j=1}^κ A^j Δt^{j+1}/(j+1)! U₀ ⊕
2Δt E U₀`, the enclosure of the difference between a constant and a time-varying input. The first
term maps `U₀` by the sum of the matrices, the second is the Minkowski sum of the `κ` images, one
per `j`, and the third the interval matrix `E = [-E, E]` scaled by `2Δt` applied to `U₀`
(`Zonotope.mtimesIntervalMat`).

Real-only, a specification: the sets and matrices are real; the rounded refinement is
`STL.depBloatingFloat`.

## Inputs
* `A` – dynamics matrix
* `U₀` – input zonotope
* `Δt` – time step
* `κ` – Taylor order

## Output
* the bloating zonotope of the input set

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 14-20]: the bloating `D` of `U₀`. -/
noncomputable def STL.depBloating (A : Mat ℝ n n) (U₀ : Zonotope (Vec ℝ n)) (Δt : ℝ) (κ : ℕ) :
    Zonotope (Vec ℝ n) :=
  let first := Zonotope.mtimes (∑ j ∈ Finset.Icc 1 κ, MatExp.particularCoeff A Δt j) U₀
  let second := (List.range κ).foldl
    (fun Z j => Z.plus (Zonotope.mtimes (MatExp.particularCoeff A Δt (j + 1)) U₀))
    (Zonotope.ofPoint 0)
  let E : Interval (Mat ℝ n n) :=
    ⟨-((2 * Δt) • MatExp.expRemainderMat A Δt κ), (2 * Δt) • MatExp.expRemainderMat A Δt κ⟩
  let third := Zonotope.mtimesIntervalMat E U₀
  (first.plus second).plus third

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
