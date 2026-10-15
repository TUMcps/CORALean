module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
public import Mathlib.Analysis.SpecialFunctions.Exp
public import CORALean.ContDynamics.LinearSys.Definitions.IsCanonicalClassicalTrajectory
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

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

# CORA's Krylov `reach` drops the constant input `c`

`reach` with `linAlg = 'krylov'` on `linearSys(0, 1, 1)` (`A = 0`, `B = 1`, `c = 1`, default
`C = 1`, `D = 0`, `k = 0`) from `R0 = {0}` with `U = {0}`: `ẋ = 1`, so the run from `0` is at
`x(Δt) = Δt`. `Krylov.reachKrylovCora1D` is CORA's first time-point set on this path; it does
not read `c`, and here it is `zonotope([0, ε, ε])` (`{0}` at `krylovError ≤ 2 eps`), within `2ε`
of `0`. So `Δt` is missed for every `krylovError = ε ∈ [0, Δt/2)` (CORA checks `ε ≥ 0`), every
`eps ≥ 0` and every order `o ≥ 2` (`o = 1` would box the two generators, the same interval). In
CORALean's `LinearSys` the input `B u + c = 1` is the input set `{1}`. The Arnoldi pass on
`[0 0; 0 0]` from `e₂` is exact, and breaks down, so the multiprecision branch is never run.

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


-- The model: CORA's code as printed, kept only to be refuted.
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


open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's first Krylov time-point set for `ẋ = 0·x + 1·u + 1`, `R0 = {0}`, `U = {0}`, step `Δt`,
misses `x(Δt) = Δt` of the run, for `0 ≤ krylovError < Δt/2`, any `eps ≥ 0` and order `o ≥ 2`. -/
theorem Krylov.reachKrylovCora1D_constant_counterexample (Δt ε eps : ℝ) (o : ℕ)
    (hε0 : 0 ≤ ε) (hε : 2 * ε < Δt) (heps : 0 ≤ eps) (ho : 2 ≤ o) :
    ∃ R, Krylov.reachKrylovCora1D 0 1 1 Δt ε eps o = some R ∧
      ∃ x w : ℝ → Vec ℝ 1,
        (LinearSys.canonical (0 : Mat ℝ 1 1) : LinearSys ℝ 1).IsCanonicalClassicalTrajectory
          (S := 𝒮) (Set.Icc 0 Δt) {0} {fun _ => 1} x w ∧
        x Δt ∉ R.construct := by -- --- PROOF ---
  -- Arnoldi on the zero matrix from `e₂`: `v⁽¹⁾ = e₂`, `h₁,₁ = h₂,₁ = 0`
  set K := Krylov.arnoldi (!![0, 1 * 0; 0, 0] : Mat ℝ 2 2) (Pi.single 1 1) 1 with hKdef
  have hK0 : K.1 0 = Pi.single 1 1 := by
    simp [K, Krylov.arnoldi, norm₂, Fin.sum_univ_two]
  have h10 : K.2 1 0 = 0 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, norm₂, Fin.sum_univ_two, dotProduct]
  have h00 : K.2 0 0 = 0 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, norm₂, Fin.sum_univ_two, dotProduct]
  -- the breakdown branch is taken and `c_new = 1 · (1 · 0) · e⁰ = 0`
  simp only [Krylov.reachKrylovCora1D, ← hKdef, h10, hK0, h00, not_lt.2 heps, if_false]
  refine ⟨_, rfl, fun s => fun _ => s, fun _ => fun _ => 1, ⟨?_, fun _ _ => rfl, ?_⟩, ?_⟩
  -- the run `x(s) = s` from `0` under the input `B u + c = 1`
  · exact funext fun _ => rfl
  · intro t _
    refine HasDerivAt.hasDerivWithinAt (hasDerivAt_pi.2 fun _ => (hasDerivAt_id t).congr_deriv ?_)
    simp
  -- every point of CORA's set is within `2 |ε|` of `0`
  intro hx
  have hred : ∀ Z : Zonotope (Vec ℝ 1), Z.h ≤ 2 → Z.reduceGirard o = Z := by
    intro Z hZ
    unfold Zonotope.reduceGirard
    rw [dif_neg (by omega)]
  by_cases hp : 2 * eps < ε
  -- `krylovError > 2 eps`: two generators `ε`, so `|Δt| ≤ 2ε`
  · simp only [hp, if_true] at hx
    rw [hred _ (by simp [Zonotope.plus, Zonotope.ofPoint]), ← Zonotope.plus_exact,
      ← Zonotope.plus_exact] at hx
    obtain ⟨y, ⟨a, ha, b, hb, rfl⟩, p, hp, hxe⟩ := hx
    rw [Zonotope.mem_ofPoint_iff] at hp
    obtain ⟨β, hβ, ha⟩ := Zonotope.mem_construct_iff.1 ha
    obtain ⟨γ, hγ, hb⟩ := Zonotope.mem_construct_iff.1 hb
    have h0 := congrFun hxe 0
    simp only [Pi.add_apply, ha 0, hb 0, hp, Fin.sum_univ_one] at h0
    simp at h0
    have h1 := abs_le.1 (hβ 0)
    have h2 := abs_le.1 (hγ 0)
    nlinarith
  -- otherwise the set is the point `0`
  · simp only [hp, if_false] at hx
    rw [hred _ (by simp [Zonotope.plus, Zonotope.ofPoint]), Zonotope.mem_construct_iff] at hx
    obtain ⟨β, -, hx⟩ := hx
    have h0 := hx 0
    simp [Zonotope.plus, Zonotope.ofPoint] at h0
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
