import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Decoupling the unknown input of a dynamical system

[1, Eq. 40]: for `rank E = n_x` the unknown input `d` is decoupled by `T̄ + N̄C = I` and `T̄D_d =
0`. Then `D_d = N̄CD_d` and `T̄ = I - N̄C`, and for `D_d` of full column rank such `T̄`, `N̄`
exist iff `rank D_d = rank CD_d`. Necessity needs no full rank: `D_d = N̄ (CD_d)` bounds `rank
D_d` by `rank CD_d`, and `rank CD_d ≤ rank D_d` always. Sufficiency: `CD_d` then has `n_d`
independent columns, a left inverse `G` with `G CD_d = I`, and `N̄ = D_d G` gives `T̄ = I - N̄C`.
## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {nx ny nd : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.descriptorDecoupleDynamic (C : Mat ℝ ny nx) (Dd : Mat ℝ nx nd)
    (hDd : Dd.rank = nd) :
    (∀ (T : Mat ℝ nx nx) (N : Mat ℝ nx ny), T + N * C = 1 → T * Dd = 0 →
      Dd = N * C * Dd ∧ T = 1 - N * C) ∧
    ((∃ (T : Mat ℝ nx nx) (N : Mat ℝ nx ny), T + N * C = 1 ∧ T * Dd = 0) ↔
      Dd.rank = (C * Dd).rank) := by -- --- PROOF ---
  -- from `T̄ + N̄C = I` and `T̄D_d = 0`
  have hT : ∀ (T : Mat ℝ nx nx) (N : Mat ℝ nx ny), T + N * C = 1 → T = 1 - N * C :=
    fun T N h => eq_sub_of_add_eq h
  have hD : ∀ (T : Mat ℝ nx nx) (N : Mat ℝ nx ny), T + N * C = 1 → T * Dd = 0 →
      Dd = N * C * Dd := by
    intro T N h h0
    have : (1 - N * C) * Dd = 0 := hT T N h ▸ h0
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    exact this
  refine ⟨fun T N h h0 => ⟨hD T N h h0, hT T N h⟩, ⟨?_, ?_⟩⟩
  · -- necessity: `D_d = N̄ (C D_d)`
    rintro ⟨T, N, h, h0⟩
    refine le_antisymm ?_ ?_
    · calc Dd.rank = (N * (C * Dd)).rank := by rw [← Matrix.mul_assoc, ← hD T N h h0]
        _ ≤ (C * Dd).rank := Matrix.rank_mul_le_right _ _
    · exact Matrix.rank_mul_le_right _ _
  · -- sufficiency: a left inverse of `C D_d`
    intro hr
    have hinj : LinearMap.ker (C * Dd).mulVecLin = ⊥ := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (C * Dd).mulVecLin
      have h2 : Module.finrank ℝ (LinearMap.range (C * Dd).mulVecLin) = nd := by
        rw [← Matrix.rank, ← hr, hDd]
      rw [h2, Module.finrank_fin_fun] at h1
      exact Submodule.finrank_eq_zero.mp (by omega)
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (C * Dd).mulVecLin hinj
    -- `N̄ = D_d G`, with `G` the matrix of `g`
    refine ⟨1 - Dd * LinearMap.toMatrix' g * C, Dd * LinearMap.toMatrix' g, ?_, ?_⟩
    · abel
    · have hG : LinearMap.toMatrix' g * (C * Dd) = 1 := by
        have hM : LinearMap.toMatrix' (C * Dd).mulVecLin = C * Dd := by
          rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
        have := congrArg LinearMap.toMatrix' hg
        rwa [LinearMap.toMatrix'_comp, hM, LinearMap.toMatrix'_id] at this
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc _ C, Matrix.mul_assoc, hG]
      simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
