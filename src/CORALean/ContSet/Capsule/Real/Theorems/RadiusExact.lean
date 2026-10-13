import CORALean.ContSet.Capsule.Real.Theorems.NormSubCentreLe
import CORALean.Global.EuclideanNorm

/-!
# `Capsule.radius` is the supremum of the distance from the centre

Every point of the capsule is within `radius` of the centre (the segment contributes at most
`‖g‖₂`, the ball `r`), and when the capsule is non-empty and the far end of the segment can be
pushed outward by `r` the bound is attained: along `g` if `g ≠ 0`, along any coordinate axis if
`g = 0` and `0 < n`. At `n = 0` with `g = 0` the only point is the centre, at distance `0`, so
`radius = r` is not attained there; the hypothesis excludes that case.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A unit vector along `g`, with `g` its multiple by `‖g‖₂`. -/
theorem aux_exists_unit_smul (g : Vec ℝ n) (hn : g ≠ 0 ∨ 0 < n) :
    ∃ u : Vec ℝ n, ‖u‖₂ = 1 ∧ g = ‖g‖₂ • u := by -- --- PROOF ---
  by_cases hg : g = 0
  · subst hg
    have hn' : 0 < n := hn.resolve_left (by simp)
    refine ⟨Pi.single ⟨0, hn'⟩ 1, ?_, by simp [norm₂_zero]⟩
    simp [norm₂, Pi.single_apply]
  · have hpos : 0 < ‖g‖₂ := by
      refine Real.sqrt_pos.mpr
        (lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun h => hg ?_)
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (g j))).mp h.symm i
        (Finset.mem_univ i)
      simpa using this
    refine ⟨‖g‖₂⁻¹ • g, ?_, ?_⟩
    · rw [norm₂_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The bound is attained, for a non-empty capsule whose far end can be pushed outward. -/
theorem Capsule.radius_isGreatest {C : Capsule n} (hr : 0 ≤ C.r) (hn : C.g ≠ 0 ∨ 0 < n) :
    IsGreatest ((fun x => ‖x - C.c‖₂) '' C.construct) C.radius := by -- --- PROOF ---
  refine ⟨?_, fun d ⟨x, hx, hd⟩ => hd ▸ Capsule.norm₂_sub_centre_le hx⟩
  obtain ⟨u, hu, hgu⟩ := aux_exists_unit_smul C.g hn
  refine ⟨C.c + (‖C.g‖₂ + C.r) • u, ⟨1, by simp, ?_⟩, ?_⟩
  · have : C.c + (‖C.g‖₂ + C.r) • u - (C.c + (1 : ℝ) • C.g) = C.r • u := by
      rw [one_smul]; nth_rewrite 2 [hgu]; rw [add_smul]; abel
    have h2 : ‖C.c + (‖C.g‖₂ + C.r) • u - (C.c + (1 : ℝ) • C.g)‖₂ ≤ C.r := by
      rw [this, norm₂_smul, hu, mul_one, abs_of_nonneg hr]
    exact h2
  · show ‖_‖₂ = _
    rw [add_sub_cancel_left, norm₂_smul, hu, mul_one,
      abs_of_nonneg (add_nonneg (norm₂_nonneg _) hr)]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
