import CORALean.Global.DmdCandidate
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Two printed statements of the dynamic mode decomposition with control that fail

[1, Eq. 3] writes `X = A X'` for `x_{k+1} = A x_k` with `X'` the time-shifted `X`; the
recursion gives `X' = A X`, and `X = A X'` fails already for `n = 1`. [1, Eq. 13] says that
for the eigenvalue `0` of `Ã = Ũᵀ X' Ṽ Σ̃⁻¹` the dynamic mode is `Ũ w`; `Ũ w` is in general
no eigenvector of `Ā = X' Ṽ Σ̃⁻¹ Ũᵀ`: for `X = [1, 0]ᵀ` and `X' = [0, 1]ᵀ` the matrix `Ã` is
`0`, `w = 1` an eigenvector for `0`, and `Ā Ũ w = [0, 1]ᵀ ≠ 0`. The mode of [1, Eq. 13],
`X' Ṽ Σ̃⁻¹ w`, is an eigenvector for `0` whenever it is nonzero (`dmd_mode_vec`).

## References

* [1] J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic mode decomposition with control".
      SIAM Journal on Applied Dynamical Systems, 15(1):142-161, 2016 (arXiv:1409.6358).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 3]: data with `X' = A X` need not satisfy `X = A X'`. -/
theorem dmd_eq3_counterexample :
    ∃ (A X X' : Mat ℝ 1 1), X' = A * X ∧ X ≠ A * X' := by -- --- PROOF ---
  refine ⟨!![2], !![1], !![2], ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this
    norm_num at this

/-- [1, Eq. 13]: for the eigenvalue `0` the mode `Ũ w` is not an eigenvector of `Ā`. -/
theorem dmd_zeroMode_counterexample :
    ∃ (X2 : Mat ℝ 2 1) (V : Mat ℝ 2 1) (s : Fin 1 → ℝ) (W : Mat ℝ 1 1) (w : Fin 1 → ℝ),
      Vᵀ * V = 1 ∧ Wᵀ * W = 1 ∧ (∀ i, s i ≠ 0) ∧
      (Vᵀ * dmdCandidate X2 V s W 1 * V) *ᵥ w = (0 : ℝ) • w ∧
      ¬ (dmdCandidate X2 V s W 1 *ᵥ (V *ᵥ w) = (0 : ℝ) • (V *ᵥ w)) := by -- --- PROOF ---
  refine ⟨!![0; 1], !![1; 0], fun _ => 1, !![1], fun _ => 1, ?_, ?_, fun _ => one_ne_zero,
    ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · funext i
    fin_cases i
    simp [dmdCandidate, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have := congrFun h 1
    simp [dmdCandidate, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
