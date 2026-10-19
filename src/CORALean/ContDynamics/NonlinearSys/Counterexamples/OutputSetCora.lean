module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.Global.Jacobian
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# `NonlinearSys.outputSetCora`, CORA's output set of `reach(nonlinearSys)`

The output set `reach` [1] stores at every time point, `outputSet(sys,R,params,options)` [2], for
an output equation `h(x, u)` that `out_isLinear` marks linear, after `validateOptions` has run
`postProcessing` [3]: `aux_set_U_uTrans_uTransVec` moves `center(U)` into `params.u` (later
`params.uTrans`) and re-centers `params.U` at the origin. `aux_outputSet` then expands `h` about
`p = [center(R); center(params.U)]` and reads `params.U` alone, never `uTrans`; at
`out_isLinear` its second- and third-order terms are `0`, so `Y = h(p) + J (R - p_x) +
D_lin (U - p_u)`. The sets are zonotopes as in CORA; the set is that of the values over
`x ∈ R`, `v ∈ params.U`, which a linear map and a sum of zonotopes give exactly.

# CORA's `nonlinearSys` output set drops the center of the input set

For `ẋ = 0`, the linear output `y = x + u`, `R0 = {0}` and the point input set `U = {1}` (the
default `u = 0`), the run `x = 0` under the input `1` has the output `1` at time `0`.
`postProcessing` moves `center(U) = 1` into `uTrans` and leaves `params.U = {0}`, and
`aux_outputSet` expands about `p_u = center(params.U) = 0` and never adds `uTrans` back, so
CORA's output set `outputSetCora` at `R0` is `{h(0, 0)} = {0}`: the output `1` is missed. It is
the set `reach` stores as its first time-point output (`outputSet(sys,params.X₀,params,options)`);
the later ones read the same `params.U`. `h` is affine, so `out_isLinear` holds and the
second- and third-order terms are `0` at either `tensorOrderOutput`.

## References

* [1] `contDynamics/@contDynamics/reach.m`
* [2] `contDynamics/@contDynamics/outputSet.m`
* [3] `global/functions/helper/dynamics/checkOptions/postProcessing.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's output set at the reachable set `R`, for the system's output equation `h = sys.g`, the
input set `U` and the nominal input `u` as the user passes them (`params.U`, `params.u`). -/
noncomputable def NonlinearSys.outputSetCora (sys : NonlinearSys n m)
    (R : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (u : Vec ℝ m) : Set (Vec ℝ sys.q) :=
  let h := sys.g                                        -- out_mFile
  -- postProcessing: aux_set_U_uTrans_uTransVec
  let centerU := U.c                                    -- centerU = center(params.U)
  let _uTrans := u + centerU                            -- params.u = params.u + center(params.U)
  let U' : Zonotope (Vec ℝ m) := ⟨U.h, U.c - centerU, U.G⟩ -- params.U = params.U + (-centerU)
  -- outputSet: aux_outputSet(sys,tensorOrderOutput,R,params)
  let p_x := R.c                                        -- p_x = center(R)
  let p_u := U'.c                                       -- p_u = center(U), U = params.U
  let zerothorder := h p_x p_u                          -- zerothorder = sys.out_mFile(p_x,p_u)
  let J := jacobianMat (fun x => h x p_u) p_x           -- [J,D_lin] = sys.out_jacobian(p_x,p_u)
  let D_lin := jacobianMat (fun v => h p_x v) p_u
  -- firstorder = J * (R + (-p_x)) + D_lin * (U + (-p_u)); secondorder = 0, thirdorder = 0
  {y | ∃ x ∈ R.construct, ∃ v ∈ U'.construct,
    y = zerothorder + J *ᵥ (x - p_x) + D_lin *ᵥ (v - p_u)}  -- Y = zerothorder + firstorder

end CORALean

namespace CORALean

open CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x = 0` under the input `1` is a run of `ẋ = 0` from `R0 = {0}` with inputs in `U = {1}`, and
its output `y = x + u = 1` is not in CORA's output set at `R0`. -/
theorem NonlinearSys.outputSetCora_counterexample : -- --- CONCL ---
    let sys : NonlinearSys 1 1 := ⟨fun _ _ => 0, 1, fun x v => x + v⟩
    let R0 : Zonotope (Vec ℝ 1) := ⟨0, 0, Fin.elim0⟩
    let U : Zonotope (Vec ℝ 1) := ⟨0, 1, Fin.elim0⟩
    let x : ℝ → Vec ℝ 1 := fun _ => 0
    let u : ℝ → Vec ℝ 1 := fun _ => 1
    let y : ℝ → Vec ℝ 1 := fun _ => 1
    sys.IsTrajectory (S := 𝒵) (Set.Ici 0) R0 U x u y ∧
      y 0 ∉ sys.outputSetCora R0 U 0 := by -- --- PROOF ---
  intro sys R0 U x u y
  refine ⟨⟨?_, fun _ _ => ?_, MeasureTheory.aestronglyMeasurable_const,
    fun _ _ => intervalIntegrable_const, continuousOn_const, fun _ _ => ?_,
    fun _ _ => by simp [sys, x, u, y]⟩, ?_⟩
  -- `R0` and `U` are the points `0` and `1`; `ẋ = 0` holds for the constant run
  · exact ⟨Fin.elim0, fun j => j.elim0, by simp [x, R0]⟩
  · exact ⟨Fin.elim0, fun j => j.elim0, by simp [u, U]⟩
  · simp [sys, x]
  -- every point of CORA's set is `h(0, 0) = 0`
  · rintro ⟨x', ⟨β, -, hx'⟩, v, ⟨γ, -, hv⟩, hy⟩
    simp only [R0, U, Finset.univ_eq_empty, Finset.sum_empty, add_zero, sub_self] at hx' hv
    subst hx' hv
    have := congrFun hy 0
    simp [sys, y, R0, U] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
