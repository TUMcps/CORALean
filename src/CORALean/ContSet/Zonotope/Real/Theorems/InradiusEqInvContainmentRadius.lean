import CORALean.ContSet.Zonotope.Real.Theorems.ZonotopeNormBallEq
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The inradius is the reciprocal of a containment radius

`[1, Eq. 20]`: `r∞(Z) = 1 / d(c + [-1, 1]ⁿ, Z)`, the largest cube centred at `c`
inside a non-degenerate `Z` against `d`, the largest `‖p - c‖_Z` over the unit cube
(the paper's Eq. 19). `ν` is homogeneous, so the cube of radius `r` fits iff
`r d ≤ 1`. The maximum `d` is attained (`ν` is continuous, the cube compact) and positive
for `n > 0`. The printed cube `[-1, -1]ⁿ` is `[-1, 1]ⁿ`, the supremum-norm unit ball.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.inradius_eq_inv_containmentRadius (Z : Zonotope (Vec ℝ n))
    (hG : Function.Surjective Z.genMap) (hn : 0 < n) :
    ∃ d, IsGreatest ((fun p => Z.zonotopeNorm (p - Z.c)) '' Metric.closedBall Z.c 1) d ∧
      IsGreatest {r | 0 ≤ r ∧ Metric.closedBall Z.c r ⊆ Z.construct}
        (1 / d) := by -- --- PROOF ---
  have hball := (Z.zonotopeNorm_ball_eq hG).1
  obtain ⟨K, hK⟩ := exists_lipschitzWith_coeffNorm Z.genMap hG
  have hcont : Continuous fun p => Z.zonotopeNorm (p - Z.c) :=
    hK.continuous.comp (continuous_id.sub continuous_const)
  obtain ⟨q, hq, hmax⟩ := (isCompact_closedBall Z.c 1).exists_isMaxOn
    ⟨Z.c, Metric.mem_closedBall_self zero_le_one⟩ hcont.continuousOn
  set d := Z.zonotopeNorm (q - Z.c) with hd
  have hhom : ∀ (a : ℝ) x, Z.zonotopeNorm (a • x) = |a| * Z.zonotopeNorm x :=
    fun a x => coeffNorm_smul _ (hG x) a
  -- `d > 0`: a unit vector has positive norm
  have hdpos : 0 < d := by
    let e : Vec ℝ n := Pi.single ⟨0, hn⟩ 1
    have he : e ≠ 0 := fun h => by simpa [e] using congrFun h ⟨0, hn⟩
    have hle : Z.zonotopeNorm e ≤ d := by
      have := hmax (show Z.c + e ∈ Metric.closedBall Z.c 1 by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        simp [e, Pi.norm_single])
      simpa using this
    exact lt_of_lt_of_le (lt_of_le_of_ne (coeffNorm_nonneg _ _)
      (Ne.symm ((coeffNorm_eq_zero_iff _ (hG e)).not.mpr he))) hle
  -- the cube of radius `r` fits iff `r d ≤ 1`
  have key : ∀ r : ℝ, 0 ≤ r → (Metric.closedBall Z.c r ⊆ Z.construct ↔ r * d ≤ 1) := by
    intro r hr
    rw [← hball]
    constructor
    -- the scaled maximizer `c + r (q - c)` lies in the smaller cube
    · intro h
      have hp := h (show Z.c + r • (q - Z.c) ∈ Metric.closedBall Z.c r by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hr]
        exact mul_le_of_le_one_right hr (by simpa [dist_eq_norm] using hq))
      simp only [Set.mem_setOf_eq, add_sub_cancel_left, hhom, abs_of_nonneg hr] at hp
      exact hp
    -- a point of the smaller cube is `r` times a point of the unit cube
    · intro h p hp
      rw [Metric.mem_closedBall, dist_eq_norm] at hp
      rcases hr.lt_or_eq with hrpos | hr0
      · have hy : Z.c + r⁻¹ • (p - Z.c) ∈ Metric.closedBall Z.c 1 := by
          rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_eq_abs, abs_inv, abs_of_pos hrpos, inv_mul_le_iff₀ hrpos, mul_one]
          exact hp
        -- so its norm is `r` times one at most `d`
        have := hmax hy
        simp only [Set.mem_setOf_eq, add_sub_cancel_left, hhom, abs_inv,
          abs_of_pos hrpos] at this
        show Z.zonotopeNorm (p - Z.c) ≤ 1
        calc Z.zonotopeNorm (p - Z.c) = r * (r⁻¹ * Z.zonotopeNorm (p - Z.c)) := by
              field_simp
          _ ≤ r * d := mul_le_mul_of_nonneg_left this hrpos.le
          _ ≤ 1 := h
      · subst hr0
        have : p = Z.c := sub_eq_zero.mp (norm_le_zero_iff.mp hp)
        show Z.zonotopeNorm (p - Z.c) ≤ 1
        rw [this, sub_self, Zonotope.zonotopeNorm, coeffNorm_zero]
        exact zero_le_one
  refine ⟨d, ⟨⟨q, hq, rfl⟩, fun _ ⟨p, hp, he⟩ => he ▸ hmax hp⟩, ⟨by positivity, ?_⟩, ?_⟩
  · exact (key _ (by positivity)).mpr (by field_simp; rfl)
  · rintro r ⟨hr, h⟩
    rw [le_div_iff₀ hdpos]
    simpa using (key r hr).mp h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
