module

public import CORALean.ContDynamics.NonlinDASys.Operations.FloatModelStackJac
public import CORALean.ContDynamics.NonlinDASys.Operations.FloatModelStackRes
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonTestFloat
public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Interval.Float.Operations.Norm

@[expose] public section

/-!
# `nonlinDASys.steadyState` in floats

CORA's loop, step for step, on a `FloatModel` and the stacked state `z = (x, y)`: `k = f` and
`l = g` are the centres of the model's enclosures at the point `(x, y, u₀)`, so are the Jacobian
blocks `A, C, D, F`, `M = [A C; D F]`, and `delta_z = M \ (-[k; l])` is the midpoint of the outward
product of an approximate inverse (`Zonotope.basisInverse`) with `-[k; l]`. The test is
`‖delta_z‖₂ < tol` (`tol² ≤ ‖delta_z‖₂²` failing, the square rounded up), the update
`z + delta_z` rounds down, and `newtonIterate` takes a `fuel` in place of CORA's unbounded loop,
over iterates stored as `Vector`s. CORA splits `delta_z` to update `x0` and `y0` each pass; the
stacked update is the same, and the split is made once, at the end.

What is returned is the candidate that passes `newtonTestFloat` for `(f, g)(·, ·, u₀)` on the
stacked state with radius `tol` (`FloatModel.stackRes`, `stackJac`), and `none` when the loop runs
out of fuel or the test fails. The certificate is the float layer's addition: CORA returns its last
iterate unchecked.
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
    let A : Mat 𝕋 n n := (fm.jacA X Y U₀).materialiseMat.centreMat
    let C : Mat 𝕋 n p := (fm.jacC X Y U₀).materialiseMat.centreMat
    let D : Mat 𝕋 p n := (fm.jacD X Y U₀).materialiseMat.centreMat
    let F : Mat 𝕋 p p := (fm.jacF X Y U₀).materialiseMat.centreMat
    -- evaluate Jacobian
    let M : Mat 𝕋 (n + p) (n + p) :=
      Fin.append (fun i => Fin.append (A i) (C i)) (fun i => Fin.append (D i) (F i))
    let Minv : Mat 𝕋 (n + p) (n + p) :=
      (Interval.point (Zonotope.basisInverse M)).materialiseMat.inf
    let delta_z : Vec 𝕋 (n + p) :=
      (Interval.mtimes Minv (Interval.point fun i => neg (Fin.append k l i))).center
    Vector.ofFn delta_z
  -- the convergence check `norm(delta_z) < 1e-10`
  let converged : Vector 𝕋 (n + p) → Bool := fun delta_z =>
    !le (mulDown tol tol) (Interval.normSq (Interval.point fun (i : Fin (n + p)) => delta_z[i]))
  -- the update of `x0` and `y0`
  letI : Add (Vector 𝕋 (n + p)) := ⟨fun a b => Vector.ofFn fun i => addDown a[i] b[i]⟩
  (newtonIterate step converged fuel (Vector.ofFn (Fin.append x₀ y₀))).bind fun zv =>
    let z : Vec 𝕋 (n + p) := fun i => zv[i]
    if NonlinDASys.newtonTestFloat (fm.stackRes U₀) (fm.stackJac U₀) z tol
    then some (fun i => z (Fin.castAdd p i), fun j => z (Fin.natAdd n j)) else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
