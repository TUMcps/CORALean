import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosureFloat
import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT
import CORALean.ContSet.MatZonotope.Float.Instances
import CORALean.ContSet.MatZonotope.Float.Operations.Point

/-!
# Sampling a continuous-time system in floats, the exponential a matrix zonotope

`discretizeMatZonotope` computed in `𝕋`: `AΔt` is the stored matrix scaled by the stored
step, a point matrix zonotope whose rounding `smul` pays into the box, and the sampled
system's matrix is its float `expMatZonoEnclosure` [1, Sec. 3.3.2]. The result is a
`LinParamSysDT` over float matrix zonotopes, whose `reach` runs through the `Mtimes`
instance `Zonotope.mtimesMatZonotope`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system a step of `Δt` leaves behind, its matrix the float matrix-zonotope
enclosure of `e^{AΔt}` at Taylor order `η`. -/
def LinearSys.discretizeMatZonotopeFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) :
    LinParamSysDT (fun m n => MatZonotope 𝕋 m n) n :=
  let AΔt := MatZonotope.smul Δt Δt (MatZonotope.point sys.A)     -- AΔt, rounded
  let eAΔt := MatExp.expMatZonoEnclosure AΔt η                      -- [e^{AΔt}]
  ⟨eAΔt⟩                                                            -- x_{k+1} ∈ [e^{AΔt}] x_k + u_k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
