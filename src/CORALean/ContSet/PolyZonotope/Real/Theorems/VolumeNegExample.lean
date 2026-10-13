import CORALean.ContSet.PolyZonotope.Real.Theorems.VolumeOfQZero

/-!
# CORA's polynomial-zonotope volume can be negative

`x = -α`, `α ∈ [-1,1]` is the interval `[-1,1]`, of volume `2`. Its Jacobian determinant is `-1`
everywhere, which is nonzero (where CORA's comment promises an exact volume), and the integral
over `[-1,1]` is `-2`. A volume is never negative, so the value is neither the volume nor an
over-approximation of it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `-α`: one factor, one generator `-1`, exponent `1`, centre `0`. -/
abbrev PolyZonotope.aux_negAlpha : PolyZonotope (Vec ℝ 1) :=
  ⟨1, 1, 0, fun _ => 0, fun _ _ => -1, fun _ _ => 1, Fin.elim0⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.volume_neg_example :
    PolyZonotope.aux_negAlpha.volume = some (-2) := by -- --- PROOF ---
  -- the derivative along the one factor is the constant `-1`
  have hconst : ∀ (k : Fin 1) (a : Fin 1 → ℝ),
      (PolyZonotope.aux_negAlpha.jacobian k).point a 0 = -1 := by
    intro k a
    fin_cases k
    simp [PolyZonotope.point, PolyZonotope.jacobian, PolyZonotope.monomial,
      PolyZonotope.aux_negAlpha]
  -- so the integral over `[-1,1]` is `-1` times the length `2`
  have hint : PolyZonotope.aux_negAlpha.jacobianDetIntegral (n := 1) rfl = -2 := by
    unfold PolyZonotope.jacobianDetIntegral
    simp only [Matrix.det_unique, Matrix.of_apply, Fin.default_eq_zero]
    refine (MeasureTheory.setIntegral_congr_fun (g := fun _ => (-1 : ℝ)) measurableSet_Icc
      (fun a _ => hconst _ a)).trans ?_
    simp only [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      Real.volume_Icc_pi, smul_eq_mul]
    simp
    norm_num
  rw [PolyZonotope.volume_of_q_zero _ rfl rfl, hint]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
