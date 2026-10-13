import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `Krylov.reachKrylovCora1D`, CORA's first Krylov time-point set in one dimension

`reach` (l. 80-81) with `linAlg = 'krylov'` runs `priv_reach_krylov` [1]; this is its first
time-point set (`aux_propagation` l. 116-156 at `k = 2`, `tStart = 0`) after
`priv_initReach_Krylov` [2] (`priv_krylov_R_uTrans`, `priv_inputSolution_Krylov`, the subspaces),
for `n = 1`, `A = a`, `B = b`, `C = cC`, from `R0 = {0}`, `U = {0}` and `u = 0`. These fix the
branches: `center(R0) = 0` and no generators leave `c_sys = g_sys = []` (`c_new = 0`); `U` has no
generators, so `Ugen = []` and `RV_0 = {0}`; `uTrans = 0`, so Arnoldi on `[a uTrans; 0 0]` from
`e₂` breaks down at once (`none` if not). `ε` is `krylovError`, `eps` MATLAB's, `o` the order.
None of these files reads `c`, `D`, `k`, `E`, `F`, `W` or `V`, so the model has no such argument.

## References

* [1] `contDynamics/@linearSys/private/priv_reach_krylov.m`
* [2] `contDynamics/@linearSys/private/priv_initReach_Krylov.m`, `priv_krylov_R_uTrans.m`,
      `priv_inputSolution_Krylov.m`, `priv_exponential_Krylov_projected_linSysInput.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's first time-point set `Rnext.tp` of `reach(linearSys)` at `linAlg = 'krylov'` in one
dimension from `R0 = {0}`, `U = {0}`, `u = 0`, at step `Δt`; `none` off the breakdown branch. -/
noncomputable def Krylov.reachKrylovCora1D (a b cC Δt ε eps : ℝ) (o : ℕ) :
    Option (Zonotope (Vec ℝ 1)) :=
  -- the zonotope [z, error*eye(1)] if krylovError > 2*eps, else [z]
  let box : ℝ → Zonotope (Vec ℝ 1) := fun z =>
    if 2 * eps < ε then ⟨1, fun _ => z, fun _ _ => ε⟩ else Zonotope.ofPoint fun _ => z
  -- priv_initReach_Krylov
  let uTrans := b * 0                               -- uTrans = linsys.B*params.uTrans
  -- priv_krylov_R_uTrans: Jawecki from e₂, Arnoldi's first pass
  let A_int : Mat ℝ 2 2 := !![a, uTrans; 0, 0]     -- A_int = [linsys.A, uTrans; zeros, 0]
  let K := Krylov.arnoldi A_int (Pi.single 1 1) 1   -- arnoldi(A_int,eqivState,krylovOrder)
  if eps < K.2 1 0 then none else                   -- H(j+1,j) <= eps: happyBreakdown, j = 1
  let V_uT := K.1 0                                 -- V = V(:,1)
  let H_uT := K.2 0 0                               -- H = Htmp(1:1,1:1)
  let V_uT_proj := cC * V_uT 0                      -- V_uT_proj = linsys.C*V_uT(1:state_dim,:)
  -- priv_inputSolution_Krylov: no generators, so inputSolV = 0 + zonotope(error_set) = {0}
  let Rpar_proj_0 := cC * 0                         -- linsys.krylov.Rpar_proj_0 = C*inputSolV
  -- aux_propagation; aux_propagate_HomSol: c_sys = [], so c_new = 0; error = krylovError*1
  let Htp := box 0                                  -- hom_tp = zonotope([c_new,G_new,error*I])
  let RV_proj := Rpar_proj_0                        -- U_0_sol numeric: RV_proj = Rpar_proj_0
  -- priv_exponential_Krylov_projected_linSysInput(uTrans_sys,[],zonotope(1),...), t = Δt
  let expMatrix := Real.exp (H_uT * Δt)             -- expMatrix = expm(c_sys.A*options.t)
  let c_new := 1 * V_uT_proj * expMatrix            -- c_new = c_norm*c_sys.B'*expMatrix(:,1)
  let RTrans_new_proj := box c_new                  -- R = zonotope([c_new,G_new,error*I])
  let U_0_sol := 0 + RV_proj                        -- U_0_sol = U_0_sol + interval(RV_proj)
  let Rhom_tp_proj := Htp.plus RTrans_new_proj      -- Rhom_tp_proj = Htp + RTrans_new_proj
  let R_tp_proj := Rhom_tp_proj.plus (Zonotope.ofPoint fun _ => U_0_sol)  -- + zonotope(U_0_sol)
  some (R_tp_proj.reduceGirard o)                   -- Rnext.tp = reduce(R_tp_proj,...)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
