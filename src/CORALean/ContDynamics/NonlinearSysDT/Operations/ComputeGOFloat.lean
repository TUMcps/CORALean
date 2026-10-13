import CORALean.ContDynamics.NonlinearSysDT.Definitions.FloatJacModel
import CORALean.ContDynamics.NonlinearSysDT.Definitions.GOFloat
import CORALean.ContDynamics.NonlinearSysDT.Operations.SimulateBoxFloat
import CORALean.ContSet.Interval.Float.Operations.DescProd
import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `NonlinearSysDT.computeGOFloat`

CORA's `nonlinearSysDT/computeGO` [1] with `compute_params = true`, as `computeGO` but over `𝕋`,
line by line with `computeGO_k` [2]: the reference run `x_ref` is a box per step (the field's
interval extension, `simulateBoxFloat`), the Jacobians `A_lin`, `B_lin`, `C_lin`, `D_lin` are
interval matrices of `fm` and `om` over that box and the point box of `u_ref`, and the products
are `Interval.descProd` and `Interval.matMul`, so every entry is rounded outward. `fm` models the
field, `om` the output equation `out_mFile`. Soundness is `computeGOFloat_outer`.

## References

* [1] `contDynamics/@nonlinearSysDT/computeGO.m`
* [2] `global/functions/helper/dynamics/contDynamics/contDynamics/computeGO_k.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The GO parameters along the reference run from `x0` under `u_ref`, as intervals enclosing
`computeGO`'s. -/
def NonlinearSysDT.computeGOFloat (fm : NonlinearSysDT.FloatJacModel 𝕋 n m n)
    (om : NonlinearSysDT.FloatJacModel 𝕋 n m r) (x0 : Vec 𝕋 n) (u_ref : ℕ → Vec 𝕋 m) :
    NonlinearSysDT.GOFloat 𝕋 n m r :=
  let x_ref := NonlinearSysDT.simulateBoxFloat ⟨fm.f⟩ x0 u_ref       -- x_ref(:,k)
  let U_ref := fun k => Interval.point (u_ref k)                    -- u_ref(:,k)
  let y_ref := fun k => om.f (x_ref k) (U_ref k)                    -- y_ref(:,k)
  let A_lin := fun k => fm.jacX (x_ref k) (U_ref k)                 -- A_lin{k}
  let B_lin := fun k => fm.jacU (x_ref k) (U_ref k)                 -- B_lin{k}
  let C_lin := fun k => om.jacX (x_ref k) (U_ref k)                 -- C_lin_k
  let D_lin := fun k => om.jacU (x_ref k) (U_ref k)                 -- D_lin_k
  let I_x := Interval.point fun (i : Fin n) (j : Fin (n + r)) =>    -- [eye(n) zeros(n, r)]
    if j.val = i.val then (one : 𝕋) else zero
  let I_y := Interval.point fun (i : Fin r) (j : Fin (n + r)) =>    -- [zeros(r, n) eye(r)]
    if j.val = n + i.val then (one : 𝕋) else zero
  { x := x_ref, y := y_ref
    -- the state parameters: A_lin{k} * A_prod, and the products times B_lin{j}, [eye 0]
    A := fun k => Interval.matMul (A_lin k) (Interval.descProd A_lin (k - 1) k)
    B := fun k j =>
      if j ≤ k then Interval.matMul (Interval.descProd A_lin k (k - j)) (B_lin j)
      else Interval.point fun _ _ => zero
    F := fun k j =>
      if j ≤ k then Interval.matMul (Interval.descProd A_lin k (k - j)) I_x
      else Interval.point fun _ _ => zero
    -- the output parameters: C_lin_k times the same products, D_lin_k and [0 eye] on the diagonal
    C := fun k => Interval.matMul (C_lin k) (Interval.descProd A_lin (k - 1) k)
    D := fun k j =>
      if j < k then
        Interval.matMul (Interval.matMul (C_lin k) (Interval.descProd A_lin (k - 1) (k - 1 - j)))
          (B_lin j)
      else if j = k then D_lin k else Interval.point fun _ _ => zero
    E := fun k j =>
      if j < k then
        Interval.matMul (Interval.matMul (C_lin k) (Interval.descProd A_lin (k - 1) (k - 1 - j)))
          I_x
      else if j = k then I_y else Interval.point fun _ _ => zero }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
