module

public import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

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
def LinParamSys.timeIntervalStepFloat (sys : LinParamSys ℐ[𝕋] n)
    (Δt : 𝕋) (η : ℕ) (R : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                                  -- [e^{AΔt}]
  let F := MatExp.intervalCorrectionMatrix sys.A Δt η                       -- [F]
  LinComb.linComb R (Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) eAΔt R) ⊞
    Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- linComb(R, e R) ⊕ F R
      (S := 𝒵[𝕋]) F R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
