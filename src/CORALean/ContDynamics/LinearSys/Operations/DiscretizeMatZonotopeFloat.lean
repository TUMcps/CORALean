module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosureFloat
public import CORALean.ContDynamics.LinParamSysDT.Operations.Canonical
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Basic

@[expose] public section

/-!
# Sampling a continuous-time system in floats, the exponential a matrix zonotope

`discretizeMatZonotope` computed in `𝕋`: `AΔt` is the stored matrix scaled by the stored
step, a point matrix zonotope whose rounding `smul` pays into the box, and the sampled
system's matrix is its float `expMatZonoEnclosure` [1, Sec. 3.3.2]. The result is a
`LinParamSysDT` over float matrix zonotopes, whose `reach` runs through the `Mtimes`
instance `Zonotope.mtimesMatZonotope`.

## Inputs
* `sys` – linear system
* `Δt` – float sampling step
* `η` – Taylor order

## Output
* sampled system whose matrix is the float matrix-zonotope enclosure

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system a step of `Δt` leaves behind, its matrix the float matrix-zonotope
enclosure of `e^{AΔt}` at Taylor order `η`. -/
def LinearSys.discretizeMatZonotopeFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) :
    LinParamSysDT (fun m n => Zonotope (Mat 𝕋 m n)) n :=
  let AΔt := Zonotope.matSmul Δt Δt (Zonotope.pointMat sys.A)     -- AΔt, rounded
  let eAΔt := MatExp.expMatZonoEnclosure AΔt η                      -- [e^{AΔt}]
  .canonical eAΔt                                                   -- x_{k+1} ∈ [e^{AΔt}] x_k + u_k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
