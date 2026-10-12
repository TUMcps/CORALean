import CORALean.ContDynamics.NonlinearSys.Operations.LinReachTensor3Cora2D
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
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

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `'lin'` step at `tensorOrder = 3` for `ẋ = (x₂³, 0)` from `{0} × [-1, 1]`, with the
derivatives and the tensor file's `ind` as generated, returns sets whose first coordinate is
`[0, 0]` for every `Δt > 0`, while the run `(t, 1)` from the initial set is at `x₁(Δt) = Δt`. -/
theorem NonlinearSys.linReachTensor3Cora2D_index_counterexample
    (quad : (Fin 2 → ℝ × ℝ) → Matrix (Fin 2) (Fin 2) (ℝ × ℝ) → ℝ × ℝ)
    (imul : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (hquad : ∀ dz, quad dz 0 = (0, 0))
    (himul : ∀ a, imul (0, 0) a = (0, 0)) (Δt : ℝ) (hΔt : 0 < Δt) (fuel : ℕ) :
    let f : (Fin 2 → ℝ) → Fin 2 → ℝ := fun x => ![x 1 ^ 3, 0]
    let jac : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun x => !![0, 3 * x 1 ^ 2; 0, 0]
    let hess : (Fin 2 → ℝ) → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
      fun x => ![!![0, 0; 0, 6 * x 1], 0]
    let T : (Fin 2 → ℝ × ℝ) → Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) (ℝ × ℝ) :=
      fun _ => ![![0, !![0, 0; 0, (6, 6)]], ![0, 0]]
    let ind : Fin 2 → List (Fin 2) := ![[1], []]
    let Rinit : Fin 2 → ℝ × ℝ := ![(0, 0), (-1, 1)]
    (∀ s : ℝ, HasDerivAt (fun s => s ^ 3) (3 * s ^ 2) s ∧
      HasDerivAt (fun s => 3 * s ^ 2) (6 * s) s ∧ HasDerivAt (fun s => 6 * s) 6 s) ∧
      (∀ x i j, j ∈ ind i ↔ T x i j ≠ 0) ∧
      (∃ R, NonlinearSys.linReachTensor3Cora2D f jac hess T ind quad imul Rinit Δt (fuel + 1) =
        some R ∧ R.1 0 = (0, 0) ∧ R.2 0 = (0, 0)) ∧
      ∃ x : ℝ → Fin 2 → ℝ, (∀ k, (Rinit k).1 ≤ x 0 k ∧ x 0 k ≤ (Rinit k).2) ∧
        (∀ t, HasDerivAt x (f (x t)) t) ∧ x Δt 0 = Δt ∧
        Δt ∉ Set.Icc (0 : ℝ) 0 := by -- --- PROOF ---
  intro f jac hess T ind Rinit
  refine ⟨fun s => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa using hasDerivAt_pow 3 s
  · exact ((hasDerivAt_pow 2 s).const_mul (3 : ℝ)).congr_deriv (by push_cast; ring)
  · simpa using (hasDerivAt_id s).const_mul (6 : ℝ)
  · -- `ind` lists the non-zero columns
    intro x i j
    fin_cases i <;> fin_cases j <;> simp [T, ind, ← Matrix.ext_iff, Fin.forall_fin_two]
  · -- the step: `p = 0`, `A = H = 0`, the remainder reads `T{1,1} = 0`
    simp [NonlinearSys.linReachTensor3Cora2D, f, jac, hess, T, ind, Rinit, abstrErrLoop, hquad,
      himul, ← Matrix.ext_iff, Fin.forall_fin_two]
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
