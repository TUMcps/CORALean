module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate
public import CORALean.Global.EuclideanNorm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `nonlinDASys.consistentInitialState`

CORA's `consistentInitialState`: Newton's method on the constraint `g(x₀, y, u₀) = 0` in `y`,
`Δy = F \ (-l)` with `l = g(x₀, y, u₀)` and `F = ∂g/∂y`, until `‖Δy‖ < 1e-10`. `F` is a
parameter, the Jacobian block CORA generates, and `tol` the `1e-10`. The iteration takes a `fuel`,
CORA's loop being unbounded; `none` is running out of it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Newton's method on `g(x₀, ·, u₀)` from `y₀`, the step `F⁻¹ (-g)`, stopping at `‖Δy‖₂ < tol`. -/
noncomputable def NonlinDASys.consistentInitialState (sys : NonlinDASys n p m)
    (F : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ p p) (tol : ℝ) (fuel : ℕ) (x₀ : Vec ℝ n)
    (u₀ : Vec ℝ m) (y₀ : Vec ℝ p) : Option (Vec ℝ p) :=
  newtonIterate (fun y => (F x₀ y u₀)⁻¹ *ᵥ (-(sys.g x₀ y u₀)))
    (fun Δ => decide (norm₂ Δ < tol)) fuel y₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
