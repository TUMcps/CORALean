module

public import CORALean.ContDynamics.LinearSys.Operations.StepErrorBox
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep

@[expose] public section

/-!
# A step's inner approximation, at a representation

In the supremum norm a ball is a box, though, and `timePointStepErrorBox` is
that box as a zonotope, so `timePointStepInnerRep` is the time-point
difference at a representation: `minkDiffRep` of the step by its error box,
at a generator representation `M` the caller offers and the operation
checks, `none` where it does not.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `X₀` – initial zonotope
* `U` – input zonotope
* `M` – generator representation

## Output
* step's end minus its error box, if the representation checks out
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The step's end minus its error box, at a representation: `none` where the
caller's generator representation `M` does not check out. -/
noncomputable def LinearSys.timePointStepInnerRep (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (X₀ U : Zonotope (Vec ℝ n))
    (M : Fin (sys.timePointStep (S := 𝒵) r η X₀ U).h →
      Fin (sys.timePointStepErrorBox r η U).h → ℝ) :
    Option (Zonotope (Vec ℝ n)) :=
  (sys.timePointStep (S := 𝒵) r η X₀ U).minkDiffRep (sys.timePointStepErrorBox r η U) M

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
