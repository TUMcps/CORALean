module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrAdaptiveTensor3Cora2D
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
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
    (hred : red (fun _ => ⟨0, 0⟩) = fun _ => ⟨0, 0⟩) :
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
