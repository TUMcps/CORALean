module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinParamSysDT.Operations.Canonical
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# Sampling a system whose matrix was already a set

`LinearSys.discretizeEnclosure` one level up. There the discretized system is set-valued only
because `e^{AΔt}` cannot be computed; here the matrix is a box to begin with, and
`expIntervalEnclosure` of `Δt • sys.A` covers both the uncertainty and the truncation. Either
way the result is a `LinParamSysDT`, so the loop of [1, Alg. 1] — `R(k) = e^{AΔt}R(k-1) ⊞ P_R(0)`,
reduced every step — is `LinParamSysDT.reach` and needs no recursion here. `ℐ` names the family.

## Inputs
* `sys` – system
* `Δt` – sampling time
* `η` – Taylor order

## Output
* the discrete-time system with the enclosed exponential

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       12-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The discrete-time system a step of `Δt` leaves behind, at a system matrix
that was a set already: `e^{AΔt}` enclosed over the whole box, as the loop of [1] uses it. -/
noncomputable def LinParamSys.discretizeEnclosure (sys : LinParamSys ℐ n) (Δt : ℝ) (η : ℕ) :
    LinParamSysDT ℐ n :=
  .canonical (MatExp.expIntervalEnclosure (Interval.smul Δt sys.A) η)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
