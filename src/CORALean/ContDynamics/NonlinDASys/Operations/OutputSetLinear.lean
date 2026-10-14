module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.Global.Jacobian

@[expose] public section

/-!
# `NonlinDASys.outputSetLinear`

The output set of `nonlinDASys/outputSet` [1] for an output equation `h(x, y, u)` that is linear
(`out_isLinear`), with the first-order term CORA's code lacks: `Y = h(p) + J_x (R - p_x) +
J_y (R_y - p_y) + J_u (U - p_u)` at `p = (p_x, p_y, p_u)` the centers of `R`, `R_y` and `U`,
the Jacobians in `x`, `y` and `u` separately. CORA's `aux_outputSet` multiplies the one
Jacobian `out_jacobian` returns, that of `x` alone, with `R` and leaves `R_y` and `U` out
(`NonlinDASys.outputSetLinearCora`). The second- and third-order terms, zero for a linear `h`,
are not defined.

## References

* [1] `contDynamics/@nonlinDASys/outputSet.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n p m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `h(p) + J_x (R - p_x) + J_y (R_y - p_y) + J_u (U - p_u)`, as the set of its values. -/
noncomputable def NonlinDASys.outputSetLinear (sys : NonlinDASys n p m)
    (p_x : Vec ℝ n) (p_y : Vec ℝ p) (p_u : Vec ℝ m) (R : S n) (R_y : S p) (U : S m) :
    Set (Vec ℝ sys.q) :=
  let zerothorder := sys.h p_x p_y p_u                              -- out_mFile(p_x,p_y,p_u)
  let J_x := jacobianMat (fun x => sys.h x p_y p_u) p_x             -- ∂h/∂x at p
  let J_y := jacobianMat (fun y => sys.h p_x y p_u) p_y             -- ∂h/∂y at p
  let J_u := jacobianMat (fun u => sys.h p_x p_y u) p_u             -- ∂h/∂u at p
  {z | ∃ x ∈ construct R, ∃ y ∈ construct R_y, ∃ u ∈ construct U,
    z = zerothorder + J_x *ᵥ (x - p_x) + J_y *ᵥ (y - p_y) + J_u *ᵥ (u - p_u)}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
