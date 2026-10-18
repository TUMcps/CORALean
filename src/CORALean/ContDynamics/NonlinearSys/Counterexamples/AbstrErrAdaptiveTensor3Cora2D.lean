module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# `abstrErrAdaptiveTensor3Cora2D`, `priv_abstractionError_adaptive` at `tensorOrder = 3`

CORA's `@nonlinearSys/private/priv_abstractionError_adaptive.m`, `alg = 'lin'`,
`tensorOrder = 3` branch (l. 110-199), in two dimensions without inputs, line by line: `H` the
Hessian at `p`, `dz = IH_x`, `errorSec = 0.5 * quadMap(Z,H)`, `[T,ind]` the tensor file over
`totalInt_x`, and the remainder loop as printed (l. 168-172): the tensor is `T{i,ind{i}(j)}`
but the factor is `dz(j)`, the position `j`, not the column `ind{i}(j)`. An all-empty `ind` gives
`errorLagr = 0`. Sets are interval hulls (`Real.Interval ℝ`) per coordinate; `err` is
`abs(center) + sum(abs(generators))` of `VerrorDyn`, i.e. `max |inf| |sup|` of its hull.

`quad dz M` is the interval `dz.'*M*dz`, `imul` the interval product, `qmap` the hull of
`quadMap(Z,H)` for `Z` the reduced `R`, `red` the hull of `reduce(VerrorDyn,'adaptive',…)`:
all arguments (the order reductions are not modelled; the zonotope is its hull, exact for a
box `VerrorDyn`).

# CORA's adaptive third-order remainder multiplies by the wrong factor

`priv_abstractionError_adaptive` at `tensorOrder = 3` (reached from `linReach_adaptive`, l. 449,
460, 492-539, for `'lin-adaptive'`) takes the right tensor `T{i,ind{i}(j)}` but the factor `dz(j)`
of the position `j` (l. 171), not `dz(ind{i}(j))`. For `ẋ₁ = x₂³`, `ẋ₂ = 0` over `Rmax = {0} ×
[-1, 1]` at `p = 0`, `ind{1}` holding column 2 only: the factor is `dz(1)`, the `x₁` range `[0,
0]`, so for every interval product that maps a zero factor to `[0, 0]` and every reduction fixing
the zero box, the returned `err` is `0`, while at `x = (0, 1)`, in the set, the Taylor remainder
of `f₁` is `1`: the error does not enclose it. The row is not the Hessian region: `p` lies in the
box, and `H(p) = 0`, `A = 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `priv_abstractionError_adaptive` (`'lin'`, `tensorOrder = 3`) in 2D without inputs:
the returned `err` for the box `Rmax` and linearization point `p`. -/
noncomputable def NonlinearSys.abstrErrAdaptiveTensor3Cora2D
    (hess : (Fin 2 → ℝ) → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : (Fin 2 → Real.Interval ℝ) → Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) (Real.Interval ℝ))
    (ind : Fin 2 → List (Fin 2))
    (quad : (Fin 2 → Real.Interval ℝ) → Matrix (Fin 2) (Fin 2) (Real.Interval ℝ) → Real.Interval ℝ)
    (imul : Real.Interval ℝ → Real.Interval ℝ → Real.Interval ℝ)
    (qmap : (Fin 2 → Real.Interval ℝ) → Matrix (Fin 2) (Fin 2) ℝ → Real.Interval ℝ)
    (red : (Fin 2 → Real.Interval ℝ) → Fin 2 → Real.Interval ℝ)
    (p : Fin 2 → ℝ) (Rmax : Fin 2 → Real.Interval ℝ) : Fin 2 → ℝ :=
  let IH_x := Rmax                                        -- IH_x = interval(R)
  let totalInt_x : Fin 2 → Real.Interval ℝ :=             -- totalInt_x = IH_x + p.x
    fun k => ⟨(IH_x k).inf + p k, (IH_x k).sup + p k⟩
  let H := hess p                                         -- H = nlnsys.hessian(p.x,p.u)
  let dz := IH_x                                          -- dz = [IH_x; IH_u]
  let errorSec : Fin 2 → Real.Interval ℝ := fun i =>                -- errorSec = 0.5 * quadMap(Z,H)
    ⟨(1 / 2) * (qmap dz (H i)).inf, (1 / 2) * (qmap dz (H i)).sup⟩
  let Tx := T totalInt_x                                  -- [T,ind] = thirdOrderTensor(totalInt)
  let errorLagr : Fin 2 → Real.Interval ℝ :=
    if (ind 0 ++ ind 1).isEmpty then fun _ => ⟨0, 0⟩         -- ind empty: errorLagr = 0
    else fun i =>                                         -- for i=1:length(ind)
      let error_sum := (List.range (ind i).length).foldl  -- for j=1:length(ind{i})
        (fun s (j : ℕ) =>
          let error_tmp := quad dz (Tx i ((ind i).getD j 0)) -- dz.'*T{i,ind{i}(j)}*dz
          let e := imul error_tmp (dz (Fin.ofNat 2 j))    -- error_tmp * dz(j)
          (⟨s.inf + e.inf, s.sup + e.sup⟩ : Real.Interval ℝ)) ⟨0, 0⟩  -- error_sum = error_sum + ...
      ⟨(1 / 6) * error_sum.inf, (1 / 6) * error_sum.sup⟩    -- errorLagr(i,1) = 1/6*error_sum
  let VerrorDyn : Fin 2 → Real.Interval ℝ := fun i =>            -- VerrorDyn = errorSec + errorLagr
    ⟨(errorSec i).inf + (errorLagr i).inf, (errorSec i).sup + (errorLagr i).sup⟩
  let VerrorDyn' := red VerrorDyn                         -- reduce(VerrorDyn,'adaptive',…)
  fun i => max |(VerrorDyn' i).inf| |(VerrorDyn' i).sup|      -- err = abs(center)+sum(abs(gens))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `priv_abstractionError_adaptive` at `tensorOrder = 3` for `ẋ = (x₂³, 0)` over
`{0} × [-1, 1]` at `p = 0` returns `err 0 = 0`, while at `(0, 1)` in the set the remainder of
`f₁` after the first- and second-order terms is `1`. -/
theorem NonlinearSys.abstrErrAdaptiveTensor3Cora2D_factor_counterexample
    (quad : (Fin 2 → Real.Interval ℝ) → Matrix (Fin 2) (Fin 2) (Real.Interval ℝ) → Real.Interval ℝ)
    (imul : Real.Interval ℝ → Real.Interval ℝ → Real.Interval ℝ)
    (himul : ∀ a, imul a ⟨0, 0⟩ = ⟨0, 0⟩)
    (qmap : (Fin 2 → Real.Interval ℝ) → Matrix (Fin 2) (Fin 2) ℝ → Real.Interval ℝ)
    (hqmap : ∀ dz, qmap dz 0 = ⟨0, 0⟩) (red : (Fin 2 → Real.Interval ℝ) → Fin 2 → Real.Interval ℝ)
    (hred : red (fun _ => ⟨0, 0⟩) = fun _ => ⟨0, 0⟩) : -- --- STMT ---
    let f : (Fin 2 → ℝ) → Fin 2 → ℝ := fun x => ![x 1 ^ 3, 0]
    let jac : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun x => !![0, 3 * x 1 ^ 2; 0, 0]
    let hess : (Fin 2 → ℝ) → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
      fun x => ![!![0, 0; 0, 6 * x 1], 0]
    let z : Real.Interval ℝ := ⟨0, 0⟩
    let Z : Matrix (Fin 2) (Fin 2) (Real.Interval ℝ) := Matrix.of fun _ _ => z
    let T : (Fin 2 → Real.Interval ℝ) → Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) (Real.Interval ℝ) :=
      fun _ => ![![Z, !![z, z; z, ⟨6, 6⟩]], ![Z, Z]]
    let ind : Fin 2 → List (Fin 2) := ![[1], []]
    let Rmax : Fin 2 → Real.Interval ℝ := ![⟨0, 0⟩, ⟨-1, 1⟩]
    (∀ s : ℝ, HasDerivAt (fun s => s ^ 3) (3 * s ^ 2) s ∧
      HasDerivAt (fun s => 3 * s ^ 2) (6 * s) s ∧ HasDerivAt (fun s => 6 * s) 6 s) ∧
      (∀ x i j, j ∈ ind i ↔ T x i j ≠ Z) ∧
      ∃ x : Fin 2 → ℝ, (∀ k, (Rmax k).inf ≤ x k - 0 ∧ x k - 0 ≤ (Rmax k).sup) ∧
        NonlinearSys.abstrErrAdaptiveTensor3Cora2D hess T ind quad imul qmap red 0 Rmax 0 <
          |f x 0 - f 0 0 - (Matrix.mulVec (jac 0) (x - 0)) 0 -
            1 / 2 * (dotProduct (x - 0) (Matrix.mulVec (hess 0 0) (x - 0)))| := by -- --- PROOF ---
  intro f jac hess z Z T ind Rmax
  refine ⟨fun s => ⟨?_, ?_, ?_⟩, ?_, ![0, 1], ?_, ?_⟩
  · simpa using hasDerivAt_pow 3 s
  · exact ((hasDerivAt_pow 2 s).const_mul (3 : ℝ)).congr_deriv (by push_cast; ring)
  · simpa using (hasDerivAt_id s).const_mul (6 : ℝ)
  · intro x i j
    fin_cases i <;> fin_cases j <;> simp [T, ind, Z, z]
    exact fun h => by have := congr_fun (congr_fun h 1) 1; simp at this
  · intro k
    fin_cases k <;> simp [Rmax]
  · -- the factor read is `dz(1) = [0, 0]`, so `err 0 = 0 < 1`
    have h : ∀ F : Fin 2 → Real.Interval ℝ, (∀ i, F i = ⟨0, 0⟩) → red F = fun _ => ⟨0, 0⟩ :=
      fun F hF => by rw [show F = fun _ => ⟨0, 0⟩ from funext hF]; exact hred
    simp only [NonlinearSys.abstrErrAdaptiveTensor3Cora2D]
    rw [h _ ?_]
    · simp [f, jac, hess, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · intro i
      fin_cases i
      · have h0 : (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
          ext a b; fin_cases a <;> fin_cases b <;> simp
        simp [hess, T, ind, Rmax, himul, h0, hqmap, List.range, List.range.loop]
      · simp [hess, T, ind, Rmax, hqmap]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
