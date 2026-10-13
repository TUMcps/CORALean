import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffDegenerateCora
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

/-!
# CORA's `minkDiff` at a degenerate minuend misses the difference entirely

The minuend is the segment `{(t, 1) | |t| ≤ 1}` (`c = (0, 1)`, `G = (1, 0)`), the subtrahend the
segment `{(t, 0) | |t| ≤ ½}`; both are degenerate and of rank one, so `@zonotope/minkDiff.m` takes
the SVD branch (`Zonotope.minkDiffDegenerateCora`). Whatever SVD `G = U S Vᵀ` the solver returns,
`U`'s first column is `±e₁`, so its first row is `±e₁ᵀ` and `P_minuend = U(1, :) = ±e₁ᵀ`: the result
`pinv(P_minuend) * Z_proj` lies on the line `x₂ = 0`, whatever the recursive 1-D call returns and
whichever method is asked for. The difference is the segment `{(t, 1) | |t| ≤ ½}`, nonempty and on
the line `x₂ = 1`: the result is neither inside it nor around it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffDegenerateCora_counterexample :
    let minuend : Zonotope (Vec ℝ 2) := ⟨1, ![0, 1], fun _ => ![1, 0]⟩
    let subtrahend : Zonotope (Vec ℝ 2) := ⟨1, 0, fun _ => ![1 / 2, 0]⟩
    ∀ (U : Mat ℝ 2 2) (S : Mat ℝ 2 1) (V : Mat ℝ 1 1), Uᵀ * U = 1 → S 1 0 = 0 →
      (!![1; 0] : Mat ℝ 2 1) = U * S * Vᵀ →
      ∀ minkDiffRec : Zonotope (Vec ℝ 1) → Zonotope (Vec ℝ 1) → Zonotope (Vec ℝ 1),
        (minkowskiDiff minuend.construct subtrahend.construct).Nonempty ∧
        Disjoint (minuend.minkDiffDegenerateCora subtrahend U 1 (by norm_num) minkDiffRec).construct
          (minkowskiDiff minuend.construct subtrahend.construct) := by -- --- PROOF ---
  intro M Sb U S V hU hS hsvd rec
  -- the SVD forces `U 1 0 = 0`, orthogonality then `U 0 1 = 0`
  have h00 := congrFun (congrFun hsvd 0) 0
  have h10 := congrFun (congrFun hsvd 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.transpose_apply,
    hS] at h00 h10
  norm_num at h00 h10
  have hU10 : U 1 0 = 0 := by
    rcases h10 with (h | h) | h
    · exact h
    · simp [h] at h00
    · simp [h] at h00
  have hc := congrFun (congrFun hU 0) 0
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hr := congrFun (congrFun hUU 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq,
    hU10] at hc hr
  have hU01 : U 0 1 = 0 := by nlinarith [sq_nonneg (U 0 1)]
  -- every point of the difference has second coordinate `1` (take `y = 0`)
  have hdiff : ∀ x ∈ minkowskiDiff M.construct Sb.construct, x 1 = 1 := by
    intro x hx
    obtain ⟨β, -, hβ⟩ := hx 0 ⟨fun _ => 0, fun _ => by simp, by simp [Sb]⟩
    have := congrFun hβ 1
    simpa [M] using this
  refine ⟨⟨![0, 1], fun y hy => ?_⟩, Set.disjoint_left.mpr fun x hx hd => ?_⟩
  · obtain ⟨β, hβ, rfl⟩ := hy
    refine ⟨fun j => β j / 2, fun j => ?_, ?_⟩
    · have := hβ j
      rw [abs_div, abs_two]
      linarith
    · funext i
      fin_cases i <;> simp [M, Sb, div_eq_mul_inv]
  · -- every point of the result has second coordinate `0`
    have h1 := hdiff x hd
    obtain ⟨β, -, rfl⟩ := hx
    simp [Zonotope.minkDiffDegenerateCora, Zonotope.mtimes, Matrix.mulVec, dotProduct,
      Finset.sum_apply, hU01] at h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
