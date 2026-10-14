module

public import CORALean.ContDynamics.NonlinearSysDT.Definitions.GO
public import CORALean.ContDynamics.NonlinearSysDT.Operations.RefState
public import CORALean.Global.DescProd
public import CORALean.Global.Jacobian
public import CORALean.Global.StackSelect

@[expose] public section

/-!
# `NonlinearSysDT.computeGO`

CORA's `nonlinearSysDT/computeGO` [1] with `compute_params = true`, `x0` a point (CORA takes the
center of a set), line by line with `computeGO_k` [2]: the Jacobians `A_lin`, `B_lin`, `C_lin`,
`D_lin` along the reference run, and the products `A_lin{k} ... A_lin{j+1}` (`descProd`).
`out` is the system's `g`, CORA's `out_mFile`.

## References

* [1] `contDynamics/@nonlinearSysDT/computeGO.m`
* [2] `global/functions/helper/dynamics/contDynamics/contDynamics/computeGO_k.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The GO parameters along the reference run from `x0` under `u_ref`. -/
noncomputable def NonlinearSysDT.computeGO (sys : NonlinearSysDT n m) (x0 : Vec ℝ n)
    (u_ref : ℕ → Vec ℝ m) : NonlinearSysDT.GO n m sys.q :=
  let out := sys.g                                                  -- out_mFile
  let x_ref := sys.refState x0 u_ref                                -- x_ref(:,k)
  let y_ref := fun k => out (x_ref k) (u_ref k)                     -- y_ref(:,k)
  let A_lin := fun k => jacobianMat (fun x => sys.f x (u_ref k)) (x_ref k)   -- A_lin{k}
  let B_lin := fun k => jacobianMat (fun u => sys.f (x_ref k) u) (u_ref k)   -- B_lin{k}
  let C_lin := fun k => jacobianMat (fun x => out x (u_ref k)) (x_ref k)     -- C_lin_k
  let D_lin := fun k => jacobianMat (fun u => out (x_ref k) u) (u_ref k)     -- D_lin_k
  { x := x_ref, y := y_ref
    A := fun k => A_lin k * descProd A_lin (k - 1) k                -- A_lin{k} * A_prod
    B := fun k j => if j ≤ k then descProd A_lin k (k - j) * B_lin j else 0
    F := fun k j => if j ≤ k then descProd A_lin k (k - j) * stackFst n sys.q else 0
    C := fun k => C_lin k * descProd A_lin (k - 1) k                -- C_lin_k * A_prod
    D := fun k j =>
      if j < k then C_lin k * descProd A_lin (k - 1) (k - 1 - j) * B_lin j
      else if j = k then D_lin k else 0
    E := fun k j =>
      if j < k then C_lin k * descProd A_lin (k - 1) (k - 1 - j) * stackFst n sys.q
      else if j = k then stackSnd n sys.q else 0 }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
