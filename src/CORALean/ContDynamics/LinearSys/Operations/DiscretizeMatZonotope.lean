module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosure
public import CORALean.ContDynamics.LinParamSysDT.Operations.Canonical
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

@[expose] public section

/-!
# Sampling a continuous-time system, the exponential enclosed by a matrix zonotope

`discretizeEnclosure` again, at a matrix zonotope in place of an interval matrix. Not a second
spelling of the same thing: an interval matrix throws away every correlation between the entries
of `e^{AΔt}`, a matrix zonotope keeps them, and that is why CORA carries `matZonotope` alongside
`intervalMatrix` [1, Sec. 3.1]. `sys.A` is one fixed matrix, so `ofPoint` is what enters the
enclosure; the width is entirely the exponential's truncation error, and it leaves the enclosure
as generators rather than as a box. `𝕄𝒵` names this family, but only `Zonotope/Real/Instances`
declares it, and that file brings instances a *use* wants and a definition does not, so the
family is written out here, as `discretizeEnclosure` writes out `ℐ`.

## Inputs
* `sys` – linear system
* `Δt` – sampling step
* `η` – Taylor order

## Output
* sampled system whose matrix is enclosed by a matrix zonotope

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar
open scoped CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system a step of `Δt` leaves behind, its matrix enclosed by a matrix
zonotope: the Taylor truncation at order `η` widened by the tail bound. -/
noncomputable def LinearSys.discretizeMatZonotope (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) :
    LinParamSysDT 𝕄𝒵 n :=
  .canonical (Real.MatExp.expMatZonoEnclosure (Real.Zonotope.ofPoint (Δt • toRealMat sys.A)) η)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
