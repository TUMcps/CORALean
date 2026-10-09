import CORALean.ContSet.ContSet.ContSet
import CORALean.Global.Jacobian

/-!
# `NonlinDASys.outputSetLinear`

The output set of `nonlinDASys/outputSet` [1] for an output equation `h(x, y, u)` that is linear
(`out_isLinear`), with the first-order term CORA's code lacks: `Y = h(p) + J_x (R - p_x) +
J_y (R_y - p_y) + J_u (U - p_u)` at `p = (p_x, p_y, p_u)` the centers of `R`, `R_y` and `U`,
the Jacobians in `x`, `y` and `u` separately. CORA's `aux_outputSet` multiplies the one
Jacobian `out_jacobian` returns, that of `x` alone, with `R` and leaves `R_y` and `U` out
(`NonlinDASys.outputSetLinearCora`). `h` has no counterpart in `NonlinDASys`, so it is an
argument; the second- and third-order terms, zero for a linear `h`, are not defined.

## References

* [1] `contDynamics/@nonlinDASys/outputSet.m`
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n p m r : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `h(p) + J_x (R - p_x) + J_y (R_y - p_y) + J_u (U - p_u)`, as the set of its values. -/
noncomputable def NonlinDASys.outputSetLinear (h : Vec ℝ n → Vec ℝ p → Vec ℝ m → Vec ℝ r)
    (p_x : Vec ℝ n) (p_y : Vec ℝ p) (p_u : Vec ℝ m) (R : S n) (R_y : S p) (U : S m) :
    Set (Vec ℝ r) :=
  let zerothorder := h p_x p_y p_u                                  -- out_mFile(p_x,p_y,p_u)
  let J_x := jacobianMat (fun x => h x p_y p_u) p_x                 -- ∂h/∂x at p
  let J_y := jacobianMat (fun y => h p_x y p_u) p_y                 -- ∂h/∂y at p
  let J_u := jacobianMat (fun u => h p_x p_y u) p_u                 -- ∂h/∂u at p
  {z | ∃ x ∈ construct R, ∃ y ∈ construct R_y, ∃ u ∈ construct U,
    z = zerothorder + J_x *ᵥ (x - p_x) + J_y *ᵥ (y - p_y) + J_u *ᵥ (u - p_u)}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
