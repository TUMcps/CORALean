module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The interval matrix `F` of the curvature set

[1, Eq. 14-20]: `F = T^(κ) A ⊕ E` with `T^(o) = ⨁_{j=2}^o [(j^{-j/(j-1)} - j^{-1/(j-1)}) Δt^j, 0]
A^{j-1}/j!` and `E = [-E, E]`, `E = e^{|A|Δt} - Σ_{j=0}^κ (|A|Δt)^j/j!`. `T^(κ) A` is read as the
interval matrix of the terms `[c_j Δt^j, 0] A^j/j!`, entry by entry as `MatExp.corrTerm`, the
order `j` of `A` computed as a point; the interval sum is the sum of the bounds. The remainder is
`MatExp.expRemainderMat`, the matrix `E` of [1] and not a scalar bound.

Real-only, a specification: the sets and matrices are real; the rounded refinement is
`STL.depCurvatureFFloat`.

## Inputs
* `A` – dynamics matrix
* `Δt` – time step
* `κ` – Taylor order

## Output
* the interval matrix of the curvature set

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

/-- [1, Eq. 14-20]: `F = T^(κ) A ⊕ E`. -/
noncomputable def STL.depCurvatureF (A : Mat ℝ n n) (Δt : ℝ) (κ : ℕ) : Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range (κ - 1), min (MatExp.corrTerm A Δt (i + 2) j k) 0)
    - MatExp.expRemainderMat A Δt κ j k
  sup := fun j k => (∑ i ∈ Finset.range (κ - 1), max (MatExp.corrTerm A Δt (i + 2) j k) 0)
    + MatExp.expRemainderMat A Δt κ j k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
