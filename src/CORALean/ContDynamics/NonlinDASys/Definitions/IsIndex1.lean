module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

/-!
# The index-1 assumption

CORA's reachability for `nonlinDASys` presumes a differentiation-index-1 system: the constraint
Jacobian `∂g/∂y` is invertible, so the constraint can be solved for `y` and the algebraic
variables carry no dynamics of their own. `IsIndex1At` is that at one point, `IsIndex1` at every
solution of the constraint. `g` is asked to be differentiable in `y`, the derivative `L` being the
Jacobian block. [1, Eq. 1] takes the DAE to be of index 1, which for the semi-explicit form holds
if and only if `det(∂g/∂y) ≠ 0` along the solution; `L.IsInvertible` is that, and CORA does not
check it. `IsIndex1` asks it at every point of the constraint, which needs no solution through the
point and implies the paper's.

## Inputs
* `sys` – system
* `x` – differential state
* `y` – algebraic variable
* `u` – input at this point

## Output
* the constraint Jacobian in `y` exists and is invertible there

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `∂g/∂y` exists and is invertible at `(x, y, u)`. -/
def NonlinDASys.IsIndex1At (sys : NonlinDASys n p m) (x : Vec ℝ n) (y : Vec ℝ p) (u : Vec ℝ m) :
    Prop :=
  ∃ L : Vec ℝ p →L[ℝ] Vec ℝ p, HasFDerivAt (fun y' => sys.g x y' u) L y ∧ L.IsInvertible

/-- `sys` is of index 1: `∂g/∂y` is invertible at every solution of the constraint. -/
def NonlinDASys.IsIndex1 (sys : NonlinDASys n p m) : Prop :=
  ∀ x y u, sys.g x y u = 0 → sys.IsIndex1At x y u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
