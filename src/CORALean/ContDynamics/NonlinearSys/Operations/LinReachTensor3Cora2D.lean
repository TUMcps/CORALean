import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# `linReachTensor3Cora2D`, CORA's `'lin'` step at `tensorOrder = 3` in two dimensions

CORA's `@contDynamics/linReach.m` at `alg = 'lin'`, `tensorOrder = 3`, default `maxError = Inf`,
line by line, with `priv_abstrerr_lin`'s `tensorOrder == 3` branch: `H` is the Hessian at `p`,
`[T,ind]` the generated tensor file over `totalInt_x`, and the remainder loop indexes `T{i,j}` and
`dz(j)` by the position `j` in `ind{i}`, as printed. Sets are carried as interval hulls `(inf, sup)`
per coordinate: only `A = f'(p) = 0` and `H(p) = 0` are modelled (else `none`), where `eAdt = I`,
`E = F = G = 0`, `Rtp = X + Δt·f0`, `Rti = enclose(X, Rtp)`, `errorSec = 0` and `priv_abstrerr_lin`
reads `R` only through `interval(R)`; there the hulls are exact (that of `enclose(X, X + v)` is the
componentwise `min`/`max`). The input column (all-zero for `U = {0}`) is left out.

`quad dz M` is CORA's interval `dz.'*M*dz` and `imul` its interval product: both are arguments.
`T x i j` is the tensor file's `T{i,j}` at `totalInt_x = x`, `ind i` its `ind{i}` (0-based); the
position `j < length(ind{i}) ≤ 2` is read as a column as `Fin.ofNat 2 j`, exact there.
The loop is `abstrErrLoop` with factor `1.1` and test `∀ i, trueError i ≤ appliedError i`, which is
MATLAB's `max(trueError./appliedError) ≤ 1` (`max` skips `NaN`, `0/0`); `fuel` bounds it.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `'lin'` step at `tensorOrder = 3` for `ẋ = f(x)` in `ℝ²` from the box `Rinit`:
`(Rti, Rtp)` as boxes, or `none` when `f'(p) ≠ 0`, `H(p) ≠ 0`, or `fuel` passes have not
settled. -/
noncomputable def NonlinearSys.linReachTensor3Cora2D (f : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (jac : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hess : (Fin 2 → ℝ) → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : (Fin 2 → ℝ × ℝ) → Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) (ℝ × ℝ))
    (ind : Fin 2 → List (Fin 2))
    (quad : (Fin 2 → ℝ × ℝ) → Matrix (Fin 2) (Fin 2) (ℝ × ℝ) → ℝ × ℝ)
    (imul : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (Rinit : Fin 2 → ℝ × ℝ) (Δt : ℝ) (fuel : ℕ) :
    Option ((Fin 2 → ℝ × ℝ) × (Fin 2 → ℝ × ℝ)) :=
  -- linearize
  let cx : Fin 2 → ℝ := fun k => ((Rinit k).1 + (Rinit k).2) / 2  -- cx = center(R)
  let f0prev := f cx                                      -- f0prev = nlnsys.mFile(cx,p.u)
  let p : Fin 2 → ℝ := fun k => cx k + f0prev k * (1 / 2) * Δt -- p.x = cx + f0prev*0.5*timeStep
  let f0 := f p                                           -- f0 = nlnsys.mFile(p.x,p.u)
  let A := jac p                                          -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A ≠ 0 then none else
  let H := hess p                                         -- H = sys.hessian(p.x,p.u)
  if H ≠ 0 then none else
  let Rdelta : Fin 2 → ℝ × ℝ := fun k => ((Rinit k).1 - p k, (Rinit k).2 - p k) -- Rinit + (-p.x)
  -- oneStep at `A = 0`
  let Pu : Fin 2 → ℝ := fun k => Δt * f0 k                -- particularSolution_constant
  let Htp : Fin 2 → ℝ × ℝ := fun k => ((Rdelta k).1 + Pu k, (Rdelta k).2 + Pu k) -- eAdt*X + Pu
  let Hti : Fin 2 → ℝ × ℝ := fun k =>                     -- Hti = enclose(X,Htp) + C_state
    (min (Rdelta k).1 (Htp k).1, max (Rdelta k).2 (Htp k).2)
  let Rtp := Htp                                          -- Rtp = Htp + PU
  let Rti := Hti                                          -- Rti = Hti + PU + C_input
  -- the true error induced by an applied one
  let Φ : (Fin 2 → ℝ) → Fin 2 → ℝ := fun appliedError =>
    let RallError : Fin 2 → ℝ := fun k => Δt * appliedError k -- particularSolution_timeVarying
    let Rmax : Fin 2 → ℝ × ℝ := fun k =>                  -- Rmax = Rti + RallError
      ((Rti k).1 - RallError k, (Rti k).2 + RallError k)
    let IHx := Rmax                                       -- IHx = interval(R)
    let totalInt : Fin 2 → ℝ × ℝ := fun k => ((IHx k).1 + p k, (IHx k).2 + p k) -- IHx + p.x
    let dz := IHx                                         -- dz = [IHx; IHu]
    let Tx := T totalInt                                  -- [T,ind] = sys.thirdOrderTensor(...)
    let errorLagr : Fin 2 → ℝ × ℝ := fun i =>             -- for i=1:length(ind)
      let error_sum := (List.range (ind i).length).foldl  -- for j=1:length(ind{i})
        (fun s (j : ℕ) =>
          let error_tmp := quad dz (Tx i (Fin.ofNat 2 j)) -- error_tmp = dz.'*T{i,j}*dz
          let e := imul error_tmp (dz (Fin.ofNat 2 j)) -- error_tmp * dz(j)
          (s.1 + e.1, s.2 + e.2)) (0, 0)                  -- error_sum = error_sum + ...
      ((1 / 6) * error_sum.1, (1 / 6) * error_sum.2)      -- errorLagr(i,1) = 1/6*error_sum
    fun i => max |(errorLagr i).1| |(errorLagr i).2|      -- trueError = sup(abs(interval(V)))
  -- while perfIndCurr > 1: appliedError = 1.1*abstrerr, from abstrerr = 0
  match abstrErrLoop (S := fun k => Fin k → ℝ) (n := 2)
      (fun te ae => decide (∀ i, te i ≤ ae i)) (fun e i => 11 / 10 * e i) Φ 0 fuel with
  | none => none
  | some trueError =>
    let Rerror : Fin 2 → ℝ := fun k => Δt * trueError k   -- particularSolution_timeVarying
    some ((fun k => ((Rti k).1 + p k - Rerror k, (Rti k).2 + p k + Rerror k)), -- Rti + p.x + Rerror
      (fun k => ((Rtp k).1 + p k - Rerror k, (Rtp k).2 + p k + Rerror k)))   -- Rtp + p.x + Rerror

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
