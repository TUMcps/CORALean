module

public import CORALean.ContDynamics.NonlinDASys.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonTestFloat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Interval.Float.Operations.Horzcat
public import CORALean.ContSet.Interval.Float.Operations.Norm
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `nonlinDASys.steadyState` in floats

CORA's loop, step for step, on a `FloatModel` and the stacked state `z = (x, y)`: `k = f` and
`l = g` are the centers of the model's enclosures at the point `(x, y, u₀)`, so are the Jacobian
blocks `A, C, D, F`, `M = [A C; D F]`, and `delta_z = M \ (-[k; l])` is the midpoint of the outward
product of an approximate inverse (`Zonotope.basisInverse`) with `-[k; l]`. The test is
`‖delta_z‖₂ < tol` (the square rounded up), the update `z + delta_z` rounds down, and
`newtonIterate` takes a `fuel` in place of CORA's unbounded loop. What is returned is the
candidate that passes `newtonTestFloat` for `(f, g)(·, ·, u₀)` on the stacked state with radius
`tol`, and `none` when the loop runs out of fuel or the test fails: CORA returns it unchecked.

## Inputs
* `fm` – float model
* `tol` – step tolerance
* `fuel` – iteration bound
* `x₀` – initial differential state
* `y₀` – initial algebraic guess
* `u₀` – fixed input

## Output
* the certified steady state, or none
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   13-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

-- file-local: only `steadyStateFloat` below needs it
/-- The Jacobian a float model returns at a point, as a matrix of floats: the `Interval` it
evaluates to is as thin as one evaluation's rounding, and its center is the matrix. -/
@[step_of NonlinDASys.FloatModel.steadyStateFloat]
def step_pointJacobian {k l : ℕ} (J : Interval (Mat 𝕋 k l)) : Mat 𝕋 k l :=
  J.materialiseMat.centerMat

/-- The slopes of `(f, g)` over a stacked box, `[A C; D F]`, at the input box `U`. -/
@[step_of NonlinDASys.FloatModel.steadyStateFloat]
def NonlinDASys.FloatModel.step_stackJac (fm : NonlinDASys.FloatModel 𝕋 n p m)
    (U : Interval (Vec 𝕋 m)) (Z : Interval (Vec 𝕋 (n + p))) : Interval (Mat 𝕋 (n + p) (n + p)) :=
  let X : Interval (Vec 𝕋 n) := ⟨fun i => Z.inf (Fin.castAdd p i), fun i => Z.sup (Fin.castAdd p i)⟩
  let Y : Interval (Vec 𝕋 p) := ⟨fun j => Z.inf (Fin.natAdd n j), fun j => Z.sup (Fin.natAdd n j)⟩
  Interval.vertcat (Interval.horzcat (fm.jacA X Y U) (fm.jacC X Y U))
    (Interval.horzcat (fm.jacD X Y U) (fm.jacF X Y U))

/-- `(f, g)` over a stacked box, at the input box `U`. -/
@[step_of NonlinDASys.FloatModel.steadyStateFloat]
def NonlinDASys.FloatModel.step_stackRes (fm : NonlinDASys.FloatModel 𝕋 n p m)
    (U : Interval (Vec 𝕋 m)) (Z : Interval (Vec 𝕋 (n + p))) : Interval (Vec 𝕋 (n + p)) :=
  let X : Interval (Vec 𝕋 n) := ⟨fun i => Z.inf (Fin.castAdd p i), fun i => Z.sup (Fin.castAdd p i)⟩
  let Y : Interval (Vec 𝕋 p) := ⟨fun j => Z.inf (Fin.natAdd n j), fun j => Z.sup (Fin.natAdd n j)⟩
  Interval.append (fm.f X Y U) (fm.g X Y U)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Newton's method on `(f, g)(·, ·, u₀)` from `(x₀, y₀)` until a stacked step of 2-norm below
`tol`, the end point returned only if a steady state within `tol` of it is certified. -/
def NonlinDASys.FloatModel.steadyStateFloat (fm : NonlinDASys.FloatModel 𝕋 n p m) (tol : 𝕋)
    (fuel : ℕ) (x₀ : Vec 𝕋 n) (y₀ : Vec 𝕋 p) (u₀ : Vec 𝕋 m) : Option (Vec 𝕋 n × Vec 𝕋 p) :=
  let U₀ : Interval (Vec 𝕋 m) := Interval.point u₀
  -- CORA's loop body on the stacked state
  let step : Vector 𝕋 (n + p) → Vector 𝕋 (n + p) := fun zv =>
    let X : Interval (Vec 𝕋 n) := Interval.point fun i => zv[Fin.castAdd p i]
    let Y : Interval (Vec 𝕋 p) := Interval.point fun j => zv[Fin.natAdd n j]
    -- returned value of dynamic equations
    let k : Vec 𝕋 n := (fm.f X Y U₀).materialise.center
    -- returned value of algebraic equations
    let l : Vec 𝕋 p := (fm.g X Y U₀).materialise.center
    -- Jacobians
    let A : Mat 𝕋 n n := step_pointJacobian (fm.jacA X Y U₀)
    let C : Mat 𝕋 n p := step_pointJacobian (fm.jacC X Y U₀)
    let D : Mat 𝕋 p n := step_pointJacobian (fm.jacD X Y U₀)
    let F : Mat 𝕋 p p := step_pointJacobian (fm.jacF X Y U₀)
    -- evaluate Jacobian
    let M : Mat 𝕋 (n + p) (n + p) :=
      Fin.append (fun i => Fin.append (A i) (C i)) (fun i => Fin.append (D i) (F i))
    let Minv : Mat 𝕋 (n + p) (n + p) :=
      (Interval.point (Zonotope.basisInverse M)).materialiseMat.inf
    let delta_z : Vec 𝕋 (n + p) :=
      (Interval.mtimes Minv (Interval.point (-(Fin.append k l)))).center
    Vector.ofFn delta_z
  -- the convergence check `norm(delta_z) < 1e-10`
  let converged : Vector 𝕋 (n + p) → Bool := fun delta_z =>
    !le (mulDown tol tol) (Interval.normSq (Interval.point fun (i : Fin (n + p)) => delta_z[i]))
  -- the update of `x0` and `y0`
  letI : Add (Vector 𝕋 (n + p)) := ⟨fun a b => Vector.ofFn fun i => addDown a[i] b[i]⟩
  (newtonIterate step converged fuel (Vector.ofFn (Fin.append x₀ y₀))).bind fun zv =>
    let z : Vec 𝕋 (n + p) := fun i => zv[i]
    if NonlinDASys.newtonTestFloat (fm.step_stackRes U₀) (fm.step_stackJac U₀) z tol
    then some (fun i => z (Fin.castAdd p i), fun j => z (Fin.natAdd n j)) else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
