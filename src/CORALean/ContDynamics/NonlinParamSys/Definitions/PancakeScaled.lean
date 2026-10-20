module

public import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# The pancake-scaled system

CORA's `aux_scaledSystem` (`guardIntersect_pancake`): `F(x, u, p) = g(x, p) f(x, u)` with the
scaling `g(x, p) = (nᵀx − d)/p`, `nᵀx = d` the guard hyperplane, oriented as CORA orients it
(`nᵀx − d > 0` on the invariant side of the reach set's center). CORA writes `F` to a file with
`matlabFunction`; here it is the function itself. The parameter is one-dimensional.

## Inputs
* `sys` – nonlinear system
* `nv` – guard normal
* `d` – guard offset

## Output
* the system scaled by the distance to the guard
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `F(x, u, p) = ((nᵀx − d)/p) f(x, u)`, `p` the one parameter. -/
noncomputable def NonlinearSys.pancakeScaled (sys : NonlinearSys n m) (nv : Vec ℝ n) (d : ℝ) :
    NonlinParamSys n m 1 where
  f x u p := ((nv ⬝ᵥ x - d) / p 0) • sys.f x u
  r := sys.q
  g x u _ := sys.g x u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
