module

public import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinParamSysDT.Operations.Canonical
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# Sampling a system with a set-valued matrix, in floats

`LinParamSys.discretizeEnclosure` computed in `𝕋`: the sampled system's matrix
is `[e^{AΔt}]` over the whole box, `expIntervalFloat` at the point range
`[Δt, Δt]`, so the result is a `LinParamSysDT` over float interval matrices,
whose `reach` runs as it stands.

## Inputs
* `sys` – system
* `Δt` – sampling time
* `η` – Taylor order

## Output
* the discrete-time system with the float-enclosed exponential

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The discrete-time system a step of `Δt` leaves behind, `e^{AΔt}` enclosed in
floats over every `A ∈ sys.A` at Taylor order `η`, as the loop of [1] uses it. -/
def LinParamSys.discretizeEnclosureFloat
    (sys : LinParamSys ℐ[𝕋] n) (Δt : 𝕋) (η : ℕ) :
    LinParamSysDT ℐ[𝕋] n :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                         -- [e^{AΔt}]
  .canonical eAΔt                                                   -- x_{k+1} ∈ [e^{AΔt}] x_k + u_k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
