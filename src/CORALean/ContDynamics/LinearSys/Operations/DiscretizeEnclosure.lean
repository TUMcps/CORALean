module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpEnclosure
public import CORALean.ContDynamics.LinParamSysDT.Operations.Canonical
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# Sampling a continuous-time system, the exponential only enclosed

`discretize` puts `e^{AΔt}` into a `LinearSysDT` as an exact real matrix, but `e^{AΔt}` is
transcendental, so nothing can compute it. `expEnclosure` is the computable enclosure, and an
enclosure is a *set* of matrices, so the discretized system is a `LinParamSysDT` over interval
matrices: the uncertainty is the numerical error of the exponential, not modelling uncertainty.
`ℐ` (`ContSet/Interval/Real/Instances`) would name the matrix family, but it comes with the
`ConvexSet`/`CompactSet`/`Mtimes` instances a *use* of this system wants and a mere definition
does not, so the family is written out here.

## Inputs
* `sys` – linear system
* `Δt` – sampling step
* `η` – Taylor order

## Output
* sampled system whose matrix is only enclosed

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar
open scoped CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system a step of `Δt` leaves behind, its matrix only enclosed: the
Taylor truncation at order `η` widened by the tail bound, [1, Thm. 1]. -/
noncomputable def LinearSys.discretizeEnclosure (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) :
    LinParamSysDT ℐ n :=
  .canonical (Real.MatExp.expEnclosure (Δt • toRealMat sys.A) η)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
