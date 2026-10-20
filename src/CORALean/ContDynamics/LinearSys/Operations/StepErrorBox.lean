module

public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepError

@[expose] public section

/-!
# A step's error ball, as a zonotope

`StepError` names a radius, and `StepInner` takes the ball of that radius off a computed step. A
ball is not a representation, so that difference is a `Set` and nothing more. In the supremum norm
`Vec ℝ n` carries, though, the ball *is* a box, `[-ε, ε]ⁿ`, and a box is the zonotope with one
generator `ε eᵢ` per coordinate: `Zonotope.closedBall_subset_diagonal` is the inclusion an error
bound needs. So the step's error, as a zonotope, is what `Zonotope.minkDiffRep` can take off a
computed step, as `LinearSysDT.reachError` is discretely, and what a whole run can carry forward
through `e^{AΔt}` and accumulate.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `U` – input zonotope

## Output
* box zonotope of the step's error radius
-/

-- Authors:       Claude Sonnet 5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `timePointStepError` bounds a point of: its radius times each unit
vector, centered at the origin. -/
noncomputable def LinearSys.timePointStepErrorBox (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (U : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  ⟨n, 0, Matrix.diagonal fun _ => sys.timePointStepError r η U⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
