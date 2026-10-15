module

public import CORALean.ContDynamics.NonlinDASys.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonTestFloat
public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Interval.Float.Operations.Norm

@[expose] public section

/-!
# `nonlinDASys.consistentInitialState` in floats

CORA's loop, step for step, on a `FloatModel`: `l = g(x₀, y, u₀)` and `F = ∂g/∂y` are the
centers of the model's enclosures at the point `(x₀, y, u₀)`, `delta_y = F \ (-l)` is the midpoint
of the outward product of an approximate inverse (`Zonotope.basisInverse`) with `-l`, the test is
`‖delta_y‖₂ < tol` (`tol² ≤ ‖delta_y‖₂²` failing, the square rounded up) and the update
`y + delta_y` rounds down. None of this is trusted: it only finds a candidate, as `newtonIterate`
with a `fuel` in place of CORA's unbounded loop. The iterates are stored as `Vector`s, and the
enclosures and the inverse materialised, so a pass reads the last iterate rather than the closure
of every pass before it.

What is returned is the candidate `y'` that passes `newtonTestFloat` for `g(x₀, ·, u₀)` with radius
`tol`, and `none` when the loop runs out of fuel or the test fails. The certificate is the float
layer's addition: CORA returns its last iterate unchecked.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Newton's method on `g(x₀, ·, u₀)` from `y₀` until a step of 2-norm below `tol`, the end point
returned only if a zero of `g(x₀, ·, u₀)` within `tol` of it is certified. -/
def NonlinDASys.FloatModel.consistentInitialStateFloat (fm : NonlinDASys.FloatModel 𝕋 n p m)
    (tol : 𝕋) (fuel : ℕ) (x₀ : Vec 𝕋 n) (u₀ : Vec 𝕋 m) (y₀ : Vec 𝕋 p) : Option (Vec 𝕋 p) :=
  let X₀ : Interval (Vec 𝕋 n) := Interval.point x₀
  let U₀ : Interval (Vec 𝕋 m) := Interval.point u₀
  -- CORA's loop body: `l`, `F` and `delta_y = F \ (-l)`
  let step : Vector 𝕋 p → Vector 𝕋 p := fun yv =>
    let Y : Interval (Vec 𝕋 p) := Interval.point fun i => yv[i]
    let l : Vec 𝕋 p := (fm.g X₀ Y U₀).materialise.center
    let F : Mat 𝕋 p p := (fm.jacF X₀ Y U₀).materialiseMat.centerMat
    let Finv : Mat 𝕋 p p := (Interval.point (Zonotope.basisInverse F)).materialiseMat.inf
    let delta_y : Vec 𝕋 p := (Interval.mtimes Finv (Interval.point (-l))).center
    Vector.ofFn delta_y
  -- the convergence check `norm(delta_y) < 1e-10`
  let converged : Vector 𝕋 p → Bool := fun delta_y =>
    !le (mulDown tol tol) (Interval.normSq (Interval.point fun (i : Fin p) => delta_y[i]))
  -- the update `y0 = y0 + delta_y`
  letI : Add (Vector 𝕋 p) := ⟨fun a b => Vector.ofFn fun i => addDown a[i] b[i]⟩
  (newtonIterate step converged fuel (Vector.ofFn y₀)).bind fun yv =>
    let y : Vec 𝕋 p := fun i => yv[i]
    if NonlinDASys.newtonTestFloat (fun Y => fm.g X₀ Y U₀) (fun Y => fm.jacF X₀ Y U₀) y tol
    then some y else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
