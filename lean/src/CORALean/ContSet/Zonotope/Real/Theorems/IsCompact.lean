import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# A zonotope is compact, hence closed

Not closed for the reason an interval is: an affine image of a merely closed set
need not be closed, so compactness is what does the work. The coefficient cube
is the closed unit ball in the supremum norm, compact because the coefficient
space is finite-dimensional, and the map onto the zonotope is continuous.

Closedness is the half an integral needs; compactness is what proves it.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   01-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

/-- The coefficient cube, as a ball, which is the form `isCompact_closedBall`
speaks about. -/
theorem Zonotope.aux_closedBall_eq (h : ℕ) :
    Metric.closedBall (0 : Fin h → ℝ) 1 = {β : Fin h → ℝ | ∀ j, |β j| ≤ 1} := by
  ext β
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq]

theorem Zonotope.aux_continuous_affine (Z : Zonotope α) :
    Continuous fun β : Fin Z.h → ℝ => Z.c + ∑ j, β j • Z.G j :=
  continuous_const.add (continuous_finsetSum _ fun j _ =>
    (continuous_apply j).smul continuous_const)

theorem Zonotope.isCompact_construct (Z : Zonotope α) : IsCompact Z.construct := by
  have himg : Z.construct
      = (fun β : Fin Z.h → ℝ => Z.c + ∑ j, β j • Z.G j) '' Metric.closedBall 0 1 := by
    rw [Zonotope.aux_closedBall_eq]
    ext x
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact ⟨β, hβ, rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      exact ⟨β, hβ, rfl⟩
  rw [himg]
  exact (isCompact_closedBall 0 1).image Z.aux_continuous_affine

theorem Zonotope.isClosed_construct (Z : Zonotope α) : IsClosed Z.construct :=
  Z.isCompact_construct.isClosed

end CORALean.Real
