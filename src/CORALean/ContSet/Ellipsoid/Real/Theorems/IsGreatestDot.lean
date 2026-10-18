module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose

@[expose] public section

/-!
# The largest value of a linear function on an ellipsoid

`max_{x ∈ E(q, Q)} lᵀ x = lᵀ q + (lᵀ Q l)^{1/2}`, the support function
[1, Sec. II (support function)] read as a maximum over the set, in the form the distance
formulas of [1, Sec. II (distances)] use: `lᵀ (q + G u) = lᵀ q + (Gᵀ l)ᵀ u`, at most
`‖Gᵀ l‖₂ = (lᵀ G Gᵀ l)^{1/2}` on the unit ball and equal to it at `u = Gᵀ l / ‖Gᵀ l‖₂`.

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". In Proc. of the 45th
      IEEE Conference on Decision and Control (CDC), pp. 1498-1503, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isGreatest_dot (E : Ellipsoid n) (l : Vec ℝ n) :
    IsGreatest ((l ⬝ᵥ ·) '' E.construct) (l ⬝ᵥ E.q + √(l ⬝ᵥ (E.Q *ᵥ l))) := by -- --- PROOF ---
  -- the ellipsoid as `q + G u`, `‖u‖₂ ≤ 1`
  simp only [Ellipsoid.construct_eq_sqrt] at *
  set w : Vec ℝ n := E.Gᵀ *ᵥ l with hw
  have hlG : ∀ u, l ⬝ᵥ (E.q + E.G *ᵥ u) = l ⬝ᵥ E.q + w ⬝ᵥ u := fun u => by
    rw [dotProduct_add, Matrix.dotProduct_mulVec, hw, Matrix.mulVec_transpose]
  have hnorm : ‖w‖₂ = √(l ⬝ᵥ (E.Q *ᵥ l)) := by
    rw [norm₂, ← E.G_mul_transpose, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
    congr 1
    simp only [dotProduct, sq]
    rfl
  rw [← hnorm]
  refine ⟨?_, ?_⟩
  -- attained at `u = w / ‖w‖₂`, or anywhere when `w = 0`
  · rcases (norm₂_nonneg w).eq_or_lt with h0 | hpos
    · refine ⟨E.q, ⟨0, by rw [norm₂_zero]; exact zero_le_one, by simp⟩, ?_⟩
      rw [← h0, add_zero]
    · refine ⟨E.q + E.G *ᵥ (‖w‖₂⁻¹ • w), ⟨_, ?_, rfl⟩, ?_⟩
      · rw [norm₂_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
      · show l ⬝ᵥ (E.q + E.G *ᵥ (‖w‖₂⁻¹ • w)) = _
        rw [hlG, dotProduct_smul, dotProduct_self, smul_eq_mul]
        field_simp
  -- Cauchy–Schwarz on the unit ball
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    show l ⬝ᵥ (E.q + E.G *ᵥ u) ≤ _
    rw [hlG]
    have := dotProduct_le_norm₂_mul_norm₂ w u
    have : ‖w‖₂ * ‖u‖₂ ≤ ‖w‖₂ := mul_le_of_le_one_right (norm₂_nonneg w) hu
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
