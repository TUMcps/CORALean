module

public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepErrorFloat
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# A step's error ball, as a float zonotope

`timePointStepErrorBox` in `𝕋`: the box `[-ε, ε]ⁿ` as the zonotope with one generator `ε eᵢ`
per coordinate, `ε` the upward-rounded radius `timePointStepErrorFloat`. Centered at the origin
with a zero error box, so its denotation is exactly that box: the error is paid once, in `ε`,
rounded up, which is the direction an inner approximation needs of the set it takes off.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `U` – input float zonotope

## Output
* float box zonotope of the step's error radius
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `timePointStepErrorFloat` bounds a point of: its radius times each unit vector. -/
def LinearSys.timePointStepErrorBoxFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (U : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let ε := sys.timePointStepErrorFloat r η U                         -- the radius, rounded up
  ⟨n, fun _ => zero, diagonalBlock fun _ => ε, Interval.point fun _ => zero⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
