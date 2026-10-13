import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm
import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Specification.STL.STL
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# The verification problem for a linear system

[1, Sec. 3]: for `ẋ = Ax + Bu`, zonotopes `X₀` and `U` and an STL formula `φ`, every trace
`ξ(·, x₀, u(·))`, `x₀ ∈ X₀`, `u(t) ∈ U` for all `t`, satisfies `φ`. [1] writes `∀t` and
`ξ(t,...) ⊨ φ`, where `⊨` takes the trace; the trace is what `Formula.Sat` takes here. The
solution is the variation-of-constants formula `LinearSys.closedForm` for a measurable
`u(·)`, with `B u` entering.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix MeasureTheory
open scoped NNReal

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3]: all traces of `ẋ = Ax + Bu` from `X₀` with inputs in `U` satisfy `φ`. -/
def STL.VerificationProblem (A : Mat ℝ n n) (B : Mat ℝ n m) (X₀ : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) (φ : STL.Formula (Vec ℝ n)) : Prop :=
  φ.HoldsOn {ξ | ∃ x₀ ∈ X₀.construct, ∃ u : ℝ → Vec ℝ m, (∀ t, 0 ≤ t → u t ∈ U.construct) ∧
    AEStronglyMeasurable u (volume.restrict (Set.Ici 0)) ∧
    ξ = fun t : ℝ≥0 => (LinearSys.mk A).closedForm x₀ (fun s => B *ᵥ u s) t}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
