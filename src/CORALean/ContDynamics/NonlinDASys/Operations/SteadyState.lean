module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonIterate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# `nonlinDASys.steadyState`

CORA's `steadyState`: Newton's method on `(f, g)(x, y, u₀) = 0` in `(x, y)`, the step
`M \ (-[k; l])` with `M = [[A, C], [D, F]]` the Jacobian blocks `∂f/∂x, ∂f/∂y, ∂g/∂x, ∂g/∂y`,
until the step has 2-norm below `1e-10`. The blocks are parameters, as in `consistentInitialState`,
the state stacked as `Fin n ⊕ Fin p → ℝ`, and the iteration takes a `fuel`.
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

/-- Newton's method on the stacked state from `(x₀, y₀)`, stopping when `‖Δz‖₂ < tol`. -/
noncomputable def NonlinDASys.steadyState (sys : NonlinDASys n p m)
    (A : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ n n) (C : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ n p)
    (D : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ p n) (F : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ p p)
    (tol : ℝ) (fuel : ℕ) (x₀ : Vec ℝ n) (y₀ : Vec ℝ p) (u₀ : Vec ℝ m) :
    Option (Vec ℝ n × Vec ℝ p) :=
  (newtonIterate (V := Fin n ⊕ Fin p → ℝ)
    (fun z =>
      let x : Vec ℝ n := fun i => z (Sum.inl i)
      let y : Vec ℝ p := fun j => z (Sum.inr j)
      (Matrix.fromBlocks (A x y u₀) (C x y u₀) (D x y u₀) (F x y u₀))⁻¹ *ᵥ
        (-(Sum.elim (sys.f x y u₀) (sys.g x y u₀))))
    (fun Δ => decide (Real.sqrt (∑ i, Δ i ^ 2) < tol)) fuel (Sum.elim x₀ y₀)).map
    fun z => ((fun i => z (Sum.inl i) : Vec ℝ n), (fun j => z (Sum.inr j) : Vec ℝ p))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
