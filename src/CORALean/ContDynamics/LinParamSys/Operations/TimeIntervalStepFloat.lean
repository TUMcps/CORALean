import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# One step of the homogeneous flow at every member, as a float zonotope

`LinParamSys.timeIntervalStep` computed in `𝕋`: `R(τ) = linComb(R, [e^{AΔt}] R) ⊕ [F] R`,
both matrices float interval enclosures over the whole box `sys.A` —
`expIntervalFloat` at the point range `[Δt, Δt]`, and
`MatExp.intervalCorrectionMatrix` at `sys.A` itself. `Δt` is a float and its own
value is the step.

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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `linComb(R, [e^{AΔt}] R) ⊕ [F] R` over every `A ∈ sys.A`, at Taylor order `η`,
[1, Alg. 4]. -/
def LinParamSys.timeIntervalStepFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (Δt : 𝕋) (η : ℕ) (R : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                                  -- [e^{AΔt}]
  let F := MatExp.intervalCorrectionMatrix sys.A Δt η                       -- [F]
  LinComb.linComb R (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k)) eAΔt R) ⊞
    Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- linComb(R, e R) ⊕ F R
      (S := fun k => Zonotope (Vec 𝕋 k)) F R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
