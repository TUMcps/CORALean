module

public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# One step of the homogeneous flow at its end, as a float zonotope

`timePointStep` without an input, computed in `𝕋`: `[e^{AΔt}] R`, the float
enclosure `expIntervalFloat` at the point range `[Δt, Δt]` applied by
`Zonotope.mtimesIntervalMat`, which carries the error box through the interval
matrix as a box. The step `reachFloat` iterates.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `R` – float state zonotope

## Output
* float zonotope at the end of the homogeneous step
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[e^{AΔt}] R` at Taylor order `η`. -/
def LinearSys.timePointStepFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (R : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                                  -- [e^{AΔt}]
  Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [e^{AΔt}] R
    (S := 𝒵[𝕋]) eAΔt R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
