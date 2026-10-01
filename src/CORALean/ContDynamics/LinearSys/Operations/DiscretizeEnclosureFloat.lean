import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT
import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat

/-!
# Sampling a continuous-time system in floats

`discretizeEnclosure` computed in `𝕋`: the sampled system's matrix is the float
interval enclosure `[e^{AΔt}]` that `expIntervalFloat` takes at the point range
`[Δt, Δt]`, so the result is a `LinParamSysDT` over float interval matrices.
Its `reach` is `LinParamSysDT.reach` at that family, which runs as it stands;
`discretizeEnclosureFloat_mem_reach` is the guarantee.

`Δt` is a float and its own value is the step: nothing rounds the time here.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system a step of `Δt` leaves behind, its matrix the float enclosure of
`e^{AΔt}` at Taylor order `η`, [1, Sec. 3.2]. -/
def LinearSys.discretizeEnclosureFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) :
    LinParamSysDT (fun m n => Interval (Mat 𝕋 m n)) n :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                         -- [e^{AΔt}]
  ⟨eAΔt⟩                                                            -- x_{k+1} ∈ [e^{AΔt}] x_k + u_k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
