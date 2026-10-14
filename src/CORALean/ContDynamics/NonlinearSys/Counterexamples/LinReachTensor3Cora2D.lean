module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# `linReachTensor3Cora2D`, CORA's `'lin'` step at `tensorOrder = 3` in two dimensions

CORA's `@contDynamics/linReach.m` at `alg = 'lin'`, `tensorOrder = 3`, default `maxError = Inf`,
line by line, with `priv_abstrerr_lin`'s `tensorOrder == 3` branch: `H` is the Hessian at `p`,
`[T,ind]` the generated tensor file over `totalInt_x`, and the remainder loop indexes `T{i,j}` and
`dz(j)` by the position `j` in `ind{i}`, as printed. Sets are carried as interval hulls
(`Real.Interval ℝ`) per coordinate: only `A = f'(p) = 0` and `H(p) = 0` are modelled (else
`none`), where `eAdt = I`,
`E = F = G = 0`, `Rtp = X + Δt·f0`, `Rti = enclose(X, Rtp)`, `errorSec = 0` and `priv_abstrerr_lin`
reads `R` only through `interval(R)`; there the hulls are exact (that of `enclose(X, X + v)` is the
componentwise `min`/`max`). The input column (all-zero for `U = {0}`) is left out.

`quad dz M` is CORA's interval `dz.'*M*dz` and `imul` its interval product: both are arguments.
`T x i j` is the tensor file's `T{i,j}` at `totalInt_x = x`, `ind i` its `ind{i}` (0-based); the
position `j < length(ind{i}) ≤ 2` is read as a column as `Fin.ofNat 2 j`, exact there.
The loop is `abstrErrLoop` with factor `1.1` and test `∀ i, trueError i ≤ appliedError i`, which is
MATLAB's `max(trueError./appliedError) ≤ 1` (`max` skips `NaN`, `0/0`); `fuel` bounds it.

# CORA's third-order remainder reads the wrong tensor columns

`priv_abstrerr_lin`'s `tensorOrder == 3` loop takes `T{i,j}*…*dz(j)` for the position `j` in
`ind{i}`, the list of non-zero columns of the tensor, where `priv_abstrerr_poly` and
`priv_linError_thirdOrder` take column `ind{i}(j)`. For `ẋ₁ = x₂³`, `ẋ₂ = 0` from
`{0} × [-1, 1]`, `ind{1}` holds column `2` only: the loop reads `T{1,1} = 0` and the remainder
is `0`, while `T{1,2}` holds `∂³f₁/∂x₂³ = 6`. At `p = 0` the Jacobian and Hessian vanish, so
CORA's step (`linReachTensor3Cora2D`), at every `Δt > 0`, for every interval kernel that maps a
zero matrix, or a zero factor, to `[0, 0]`, accepts on its first pass and keeps `x₁` at `[0, 0]`
in both `Rti` and `Rtp`; the run from `(0, 1)` is `(t, 1)`, at `x₁(Δt) = Δt`. The miss is the
index, not the region: `p` lies in the box the tensor is read over.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `'lin'` step at `tensorOrder = 3` for `ẋ = f(x)` in `ℝ²` from the box `Rinit`:
`(Rti, Rtp)` as boxes, or `none` when `f'(p) ≠ 0`, `H(p) ≠ 0`, or `fuel` passes have not
settled. -/
noncomputable def NonlinearSys.linReachTensor3Cora2D (f : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (jac : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hess : (Fin 2 → ℝ) → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : (Fin 2 → Real.Interval ℝ) → Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) (Real.Interval ℝ))
    (ind : Fin 2 → List (Fin 2))
    (quad : (Fin 2 → Real.Interval ℝ) → Matrix (Fin 2) (Fin 2) (Real.Interval ℝ) → Real.Interval ℝ)
    (imul : Real.Interval ℝ → Real.Interval ℝ → Real.Interval ℝ)
    (Rinit : Fin 2 → Real.Interval ℝ) (Δt : ℝ) (fuel : ℕ) :
    Option ((Fin 2 → Real.Interval ℝ) × (Fin 2 → Real.Interval ℝ)) :=
  -- linearize
  let cx : Fin 2 → ℝ := fun k => ((Rinit k).inf + (Rinit k).sup) / 2  -- cx = center(R)
  let f0prev := f cx                                      -- f0prev = nlnsys.mFile(cx,p.u)
  let p : Fin 2 → ℝ := fun k => cx k + f0prev k * (1 / 2) * Δt -- p.x = cx + f0prev*0.5*timeStep
  let f0 := f p                                           -- f0 = nlnsys.mFile(p.x,p.u)
  let A := jac p                                          -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A ≠ 0 then none else
  let H := hess p                                         -- H = sys.hessian(p.x,p.u)
  if H ≠ 0 then none else
  -- Rinit + (-p.x)
  let Rdelta : Fin 2 → Real.Interval ℝ := fun k => ⟨(Rinit k).inf - p k, (Rinit k).sup - p k⟩
  -- oneStep at `A = 0`
  let Pu : Fin 2 → ℝ := fun k => Δt * f0 k                -- particularSolution_constant
  -- eAdt*X + Pu
  let Htp : Fin 2 → Real.Interval ℝ := fun k => ⟨(Rdelta k).inf + Pu k, (Rdelta k).sup + Pu k⟩
  let Hti : Fin 2 → Real.Interval ℝ := fun k =>                    -- Hti = enclose(X,Htp) + C_state
    ⟨min (Rdelta k).inf (Htp k).inf, max (Rdelta k).sup (Htp k).sup⟩
  let Rtp := Htp                                          -- Rtp = Htp + PU
  let Rti := Hti                                          -- Rti = Hti + PU + C_input
  -- the true error induced by an applied one
  let Φ : (Fin 2 → ℝ) → Fin 2 → ℝ := fun appliedError =>
    let RallError : Fin 2 → ℝ := fun k => Δt * appliedError k -- particularSolution_timeVarying
    let Rmax : Fin 2 → Real.Interval ℝ := fun k =>                  -- Rmax = Rti + RallError
      ⟨(Rti k).inf - RallError k, (Rti k).sup + RallError k⟩
    let IHx := Rmax                                       -- IHx = interval(R)
    -- IHx + p.x
    let totalInt : Fin 2 → Real.Interval ℝ := fun k => ⟨(IHx k).inf + p k, (IHx k).sup + p k⟩
    let dz := IHx                                         -- dz = [IHx; IHu]
    let Tx := T totalInt                                  -- [T,ind] = sys.thirdOrderTensor(...)
    let errorLagr : Fin 2 → Real.Interval ℝ := fun i =>             -- for i=1:length(ind)
      let error_sum := (List.range (ind i).length).foldl  -- for j=1:length(ind{i})
        (fun s (j : ℕ) =>
          let error_tmp := quad dz (Tx i (Fin.ofNat 2 j)) -- error_tmp = dz.'*T{i,j}*dz
          let e := imul error_tmp (dz (Fin.ofNat 2 j)) -- error_tmp * dz(j)
          (⟨s.inf + e.inf, s.sup + e.sup⟩ : Real.Interval ℝ)) ⟨0, 0⟩  -- error_sum = error_sum + ...
      ⟨(1 / 6) * error_sum.inf, (1 / 6) * error_sum.sup⟩    -- errorLagr(i,1) = 1/6*error_sum
    fun i => max |(errorLagr i).inf| |(errorLagr i).sup|      -- trueError = sup(abs(interval(V)))
  -- while perfIndCurr > 1: appliedError = 1.1*abstrerr, from abstrerr = 0
  match abstrErrLoop (S := fun k => Fin k → ℝ) (n := 2)
      (fun te ae => decide (∀ i, te i ≤ ae i)) (fun e i => 11 / 10 * e i) Φ 0 fuel with
  | none => none
  | some trueError =>
    let Rerror : Fin 2 → ℝ := fun k => Δt * trueError k   -- particularSolution_timeVarying
    -- Rti + p.x + Rerror
    some ((fun k => ⟨(Rti k).inf + p k - Rerror k, (Rti k).sup + p k + Rerror k⟩),
      (fun k => ⟨(Rtp k).inf + p k - Rerror k, (Rtp k).sup + p k + Rerror k⟩)) -- Rtp + p.x + Rerror


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `'lin'` step at `tensorOrder = 3` for `ẋ = (x₂³, 0)` from `{0} × [-1, 1]`, with the
derivatives and the tensor file's `ind` as generated, returns sets whose first coordinate is
`[0, 0]` for every `Δt > 0`, while the run `(t, 1)` from the initial set is at `x₁(Δt) = Δt`. -/
theorem NonlinearSys.linReachTensor3Cora2D_index_counterexample
    (quad : (Fin 2 → Real.Interval ℝ) → Matrix (Fin 2) (Fin 2) (Real.Interval ℝ) → Real.Interval ℝ)
    (imul : Real.Interval ℝ → Real.Interval ℝ → Real.Interval ℝ)
    (hquad : ∀ dz, quad dz (Matrix.of fun _ _ => ⟨0, 0⟩) = ⟨0, 0⟩)
    (himul : ∀ a, imul ⟨0, 0⟩ a = ⟨0, 0⟩) (Δt : ℝ) (hΔt : 0 < Δt) (fuel : ℕ) :
    let f : (Fin 2 → ℝ) → Fin 2 → ℝ := fun x => ![x 1 ^ 3, 0]
    let jac : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun x => !![0, 3 * x 1 ^ 2; 0, 0]
    let hess : (Fin 2 → ℝ) → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
      fun x => ![!![0, 0; 0, 6 * x 1], 0]
    let z : Real.Interval ℝ := ⟨0, 0⟩
    let Z : Matrix (Fin 2) (Fin 2) (Real.Interval ℝ) := Matrix.of fun _ _ => z
    let T : (Fin 2 → Real.Interval ℝ) → Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) (Real.Interval ℝ) :=
      fun _ => ![![Z, !![z, z; z, ⟨6, 6⟩]], ![Z, Z]]
    let ind : Fin 2 → List (Fin 2) := ![[1], []]
    let Rinit : Fin 2 → Real.Interval ℝ := ![⟨0, 0⟩, ⟨-1, 1⟩]
    (∀ s : ℝ, HasDerivAt (fun s => s ^ 3) (3 * s ^ 2) s ∧
      HasDerivAt (fun s => 3 * s ^ 2) (6 * s) s ∧ HasDerivAt (fun s => 6 * s) 6 s) ∧
      (∀ x i j, j ∈ ind i ↔ T x i j ≠ Z) ∧
      (∃ R, NonlinearSys.linReachTensor3Cora2D f jac hess T ind quad imul Rinit Δt (fuel + 1) =
        some R ∧ R.1 0 = ⟨0, 0⟩ ∧ R.2 0 = ⟨0, 0⟩) ∧
      ∃ x : ℝ → Fin 2 → ℝ, (∀ k, (Rinit k).inf ≤ x 0 k ∧ x 0 k ≤ (Rinit k).sup) ∧
        (∀ t, HasDerivAt x (f (x t)) t) ∧ x Δt 0 = Δt ∧
        Δt ∉ Set.Icc (0 : ℝ) 0 := by -- --- PROOF ---
  intro f jac hess z Z T ind Rinit
  refine ⟨fun s => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa using hasDerivAt_pow 3 s
  · exact ((hasDerivAt_pow 2 s).const_mul (3 : ℝ)).congr_deriv (by push_cast; ring)
  · simpa using (hasDerivAt_id s).const_mul (6 : ℝ)
  · -- `ind` lists the non-zero columns
    intro x i j
    fin_cases i <;> fin_cases j <;> simp [T, ind, Z, z]
    exact fun h => by have := congr_fun (congr_fun h 1) 1; simp at this
  · -- the step: `p = 0`, `A = H = 0`, the remainder reads `T{1,1} = 0`
    simp [NonlinearSys.linReachTensor3Cora2D, f, jac, hess, T, ind, Rinit, abstrErrLoop, hquad,
      himul, Z, z, ← Matrix.ext_iff, Fin.forall_fin_two]
  · -- the run `(t, 1)`
    refine ⟨fun t => ![t, 1], ?_, fun t => ?_, by simp, by simp [hΔt.ne']⟩
    · intro k
      fin_cases k <;> simp [Rinit]
    · rw [hasDerivAt_pi]
      intro k
      fin_cases k
      · simpa [f] using hasDerivAt_id' t
      · simpa [f] using hasDerivAt_const t (1 : ℝ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
