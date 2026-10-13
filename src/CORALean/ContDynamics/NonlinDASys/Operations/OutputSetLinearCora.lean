import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.Global.Jacobian

/-!
# `NonlinDASys.outputSetLinearCora`

The output set CORA's `nonlinDASys/outputSet` [1] computes in `aux_outputSet` for an output
equation `h(x, y, u)` that is linear (`out_isLinear`): `second order = third order = 0`, so
`Y = h(p) + J (R - p_x)` with `p = (p_x, p_y, p_u)` the centers of `R`, `R_y` and `U`, and `J` the
Jacobian `out_jacobian` returns first, that of `h` in `x` alone: `Jout.x`, `Jout.u` are the only
Jacobians `derivatives` writes for a system with algebraic variables, and `outputSet` reads the
first. The algebraic set `R_y` and the input set `U` enter only through their centers.
`h` has no counterpart in `NonlinDASys`, so it is an argument.

## References

* [1] `contDynamics/@nonlinDASys/outputSet.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n p m r : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `h(p) + J (R + (-p_x))`, `J = ∂h/∂x` at `p`, as the set of its values over `x ∈ R`. -/
noncomputable def NonlinDASys.outputSetLinearCora (h : Vec ℝ n → Vec ℝ p → Vec ℝ m → Vec ℝ r)
    (p_x : Vec ℝ n) (p_y : Vec ℝ p) (p_u : Vec ℝ m) (R : S n) : Set (Vec ℝ r) :=
  let zerothorder := h p_x p_y p_u                                  -- out_mFile(p_x,p_y,p_u)
  let J := jacobianMat (fun x => h x p_y p_u) p_x                   -- out_jacobian(p_x,p_y,p_u)
  {z | ∃ x ∈ construct R, z = zerothorder + J *ᵥ (x - p_x)}        -- zerothorder + firstorder

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
