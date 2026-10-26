module

public import CORALean.ContDynamics.NonlinDASys.Definitions.OutputFloatModel
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Point

@[expose] public section

/-!
# `NonlinDASys.OutputFloatModel.outputSetLinearFloat`

`NonlinDASys.outputSetLinear` in floats, one `let` per `let` of the real one: the value `h(p)` is
the box the model gives at the point boxes of the centers `p`, converted to a zonotope, and each
Jacobian block the model's box at the same point boxes, applied to the set shifted by its center
(`R - p_x`, `R_y - p_y`, `U - p_u`) by `Zonotope.mtimesIntervalMat`. Every sum and product is
outward-rounded, the rounding kept in the error box.

## Inputs
* `om` – float model of the output equation
* `p_x` – state center
* `p_y` – algebraic center
* `p_u` – input center
* `R` – float state set
* `R_y` – float algebraic set
* `U` – float input set

## Output
* float zonotope of the linear output equation's values
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet Plus

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinDASys.OutputFloatModel.outputSetLinearFloat (om : NonlinDASys.OutputFloatModel 𝕋 n p m q)
    (p_x : Vec 𝕋 n) (p_y : Vec 𝕋 p) (p_u : Vec 𝕋 m) (R : Zonotope (Vec 𝕋 n))
    (R_y : Zonotope (Vec 𝕋 p)) (U : Zonotope (Vec 𝕋 m)) : Zonotope (Vec 𝕋 q) :=
  let P_x := Interval.point p_x                                     -- the point boxes of `p`
  let P_y := Interval.point p_y
  let P_u := Interval.point p_u
  let zerothorder := (om.h P_x P_y P_u).zonotope                    -- out_mFile(p_x,p_y,p_u)
  let J_x := om.jacX P_x P_y P_u                                    -- ∂h/∂x at p
  let J_y := om.jacY P_x P_y P_u                                    -- ∂h/∂y at p
  let J_u := om.jacU P_x P_y P_u                                    -- ∂h/∂u at p
  ((zerothorder ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) J_x (R ⊞ Zonotope.point (-p_x))) ⊞
    Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) J_y (R_y ⊞ Zonotope.point (-p_y))) ⊞
    Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) J_u (U ⊞ Zonotope.point (-p_u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
