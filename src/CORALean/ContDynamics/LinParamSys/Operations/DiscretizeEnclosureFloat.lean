import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

/-!
# Sampling a system with a set-valued matrix, in floats

`LinParamSys.discretizeEnclosure` computed in `𝕋`: the sampled system's matrix
is `[e^{AΔt}]` over the whole box, `expIntervalFloat` at the point range
`[Δt, Δt]`, so the result is a `LinParamSysDT` over float interval matrices,
whose `reach` runs as it stands.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The discrete-time system a step of `Δt` leaves behind, `e^{AΔt}` enclosed in
floats over every `A ∈ sys.A` at Taylor order `η`, [1, Alg. 4]. -/
def LinParamSys.discretizeEnclosureFloat
    (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n) (Δt : 𝕋) (η : ℕ) :
    LinParamSysDT (fun m n => Interval (Mat 𝕋 m n)) n :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                         -- [e^{AΔt}]
  ⟨eAΔt⟩                                                            -- x_{k+1} ∈ [e^{AΔt}] x_k + u_k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
