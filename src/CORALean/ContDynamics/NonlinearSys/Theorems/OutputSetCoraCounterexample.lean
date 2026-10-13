import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.NonlinearSys.Operations.OutputSetCora
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# CORA's `nonlinearSys` output set drops the centre of the input set

For `ẋ = 0`, the linear output `y = x + u`, `R0 = {0}` and the point input set `U = {1}` (the
default `u = 0`), the run `x = 0` under the input `1` has the output `1` at time `0`.
`postProcessing` moves `center(U) = 1` into `uTrans` and leaves `params.U = {0}`, and
`aux_outputSet` expands about `p_u = center(params.U) = 0` and never adds `uTrans` back, so
CORA's output set `outputSetCora` at `R0` is `{h(0, 0)} = {0}`: the output `1` is missed. It is
the set `reach` stores as its first time-point output (`outputSet(sys,params.X₀,params,options)`);
the later ones read the same `params.U`. `h` is affine, so `out_isLinear` holds and the
second- and third-order terms are `0` at either `tensorOrderOutput`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x = 0` under the input `1` is a run of `ẋ = 0` from `R0 = {0}` with inputs in `U = {1}`, and
its output `x(0) + u(0) = 1` is not in CORA's output set at `R0`. -/
theorem NonlinearSys.outputSetCora_counterexample :
    let sys : NonlinearSys 1 1 := ⟨fun _ _ => 0⟩
    let h : Vec ℝ 1 → Vec ℝ 1 → Vec ℝ 1 := fun x v => x + v
    let R0 : Zonotope (Vec ℝ 1) := ⟨0, 0, Fin.elim0⟩
    let U : Zonotope (Vec ℝ 1) := ⟨0, 1, Fin.elim0⟩
    let x : ℝ → Vec ℝ 1 := fun _ => 0
    let u : ℝ → Vec ℝ 1 := fun _ => 1
    sys.Trajectory (S := fun n => Zonotope (Vec ℝ n)) (Set.Ici 0) R0 U x u ∧
      h (x 0) (u 0) ∉ NonlinearSys.outputSetCora h R0 U 0 := by -- --- PROOF ---
  intro sys h R0 U x u
  refine ⟨⟨?_, fun _ _ => ?_, fun _ _ => ?_⟩, ?_⟩
  -- `R0` and `U` are the points `0` and `1`; `ẋ = 0` holds for the constant run
  · exact ⟨Fin.elim0, fun j => j.elim0, by simp [x, R0]⟩
  · exact ⟨Fin.elim0, fun j => j.elim0, by simp [u, U]⟩
  · exact hasDerivWithinAt_const _ _ _
  -- every point of CORA's set is `h(0, 0) = 0`
  · rintro ⟨x', ⟨β, -, hx'⟩, v, ⟨γ, -, hv⟩, hy⟩
    simp only [R0, U, Finset.univ_eq_empty, Finset.sum_empty, add_zero, sub_self] at hx' hv
    subst hx' hv
    have := congrFun hy 0
    simp [h, x, u, R0, U] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
