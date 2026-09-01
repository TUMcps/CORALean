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
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- The coefficient cube, as a ball, which is the form `isCompact_closedBall`
speaks about. -/
theorem Zonotope.aux_closedBall_eq (h : ℕ) :
    Metric.closedBall (0 : Vec ℝ h) 1 = {β : Vec ℝ h | ∀ j, |β j| ≤ 1} := by
  ext β
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq]

theorem Zonotope.aux_continuous_affine (Z : Zonotope n) :
    Continuous fun β : Vec ℝ Z.h => (fun i => Z.c i + ∑ j, Z.G i j * β j : Vec ℝ n) :=
  continuous_pi fun _ =>
    continuous_const.add (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_apply j))

theorem Zonotope.isCompact_construct (Z : Zonotope n) : IsCompact Z.construct := by
  have himg : Z.construct
      = (fun β : Vec ℝ Z.h => (fun i => Z.c i + ∑ j, Z.G i j * β j : Vec ℝ n))
        '' Metric.closedBall 0 1 := by
    rw [Zonotope.aux_closedBall_eq]
    ext x
    constructor
    · rintro ⟨β, hβ, hx⟩
      exact ⟨β, hβ, (funext fun i => (hx i).symm)⟩
    · rintro ⟨β, hβ, rfl⟩
      exact ⟨β, hβ, fun _ => rfl⟩
  rw [himg]
  exact (isCompact_closedBall 0 1).image Z.aux_continuous_affine

theorem Zonotope.isClosed_construct (Z : Zonotope n) : IsClosed Z.construct :=
  Z.isCompact_construct.isClosed

end CORALean.Real
