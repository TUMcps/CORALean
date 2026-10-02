import CORALean.ContDynamics.NonlinDASys.NonlinDASys

/-!
# The index-1 assumption

CORA's reachability for `nonlinDASys` presumes a differentiation-index-1 system: the constraint
Jacobian `∂g/∂y` is invertible, so the constraint can be solved for `y` and the algebraic
variables carry no dynamics of their own. `Index1At` is that at one point, `Index1` at every
solution of the constraint. `g` is asked to be differentiable in `y`, the derivative `L` being
the Jacobian block; it is a hypothesis wherever it is spent, not a field of the class.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `∂g/∂y` exists and is invertible at `(x, y, u)`. -/
def NonlinDASys.Index1At (sys : NonlinDASys n p m) (x : Vec ℝ n) (y : Vec ℝ p) (u : Vec ℝ m) :
    Prop :=
  ∃ L : Vec ℝ p →L[ℝ] Vec ℝ p, HasFDerivAt (fun y' => sys.g x y' u) L y ∧ L.IsInvertible

/-- `sys` is of index 1: `∂g/∂y` is invertible at every solution of the constraint. -/
def NonlinDASys.Index1 (sys : NonlinDASys n p m) : Prop :=
  ∀ x y u, sys.g x y u = 0 → sys.Index1At x y u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
