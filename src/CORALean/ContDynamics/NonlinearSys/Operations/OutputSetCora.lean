module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Jacobian

@[expose] public section

/-!
# `NonlinearSys.outputSetCora`, CORA's output set of `reach(nonlinearSys)`

The output set `reach` [1] stores at every time point, `outputSet(sys,R,params,options)` [2], for
an output equation `h(x, u)` that `out_isLinear` marks linear, after `validateOptions` has run
`postProcessing` [3]: `aux_set_U_uTrans_uTransVec` moves `center(U)` into `params.u` (later
`params.uTrans`) and re-centres `params.U` at the origin. `aux_outputSet` then expands `h` about
`p = [center(R); center(params.U)]` and reads `params.U` alone, never `uTrans`; at
`out_isLinear` its second- and third-order terms are `0`, so `Y = h(p) + J (R - p_x) +
D_lin (U - p_u)`. The sets are zonotopes as in CORA; the set is that of the values over
`x ∈ R`, `v ∈ params.U`, which a linear map and a sum of zonotopes give exactly.

## References

* [1] `contDynamics/@contDynamics/reach.m`
* [2] `contDynamics/@contDynamics/outputSet.m`
* [3] `global/functions/helper/dynamics/checkOptions/postProcessing.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's output set at the reachable set `R`, for the output equation `h`, the input set `U` and
the nominal input `u` as the user passes them (`params.U`, `params.u`). -/
noncomputable def NonlinearSys.outputSetCora (h : Vec ℝ n → Vec ℝ m → Vec ℝ r)
    (R : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (u : Vec ℝ m) : Set (Vec ℝ r) :=
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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
