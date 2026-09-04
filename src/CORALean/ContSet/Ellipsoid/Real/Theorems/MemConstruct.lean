import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# What an ellipsoid contains

Two introductions rather than a characterisation: the affine image of a ball
point, and the centre, which is that image at `u = 0`.

The centre is what makes the representation never empty, and it is where the
support function's maximum is attained when the direction is one `G` collapses.
Each is a line, and both are the same statement at different `u`, so they share
a file.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

theorem Ellipsoid.mem_construct {E : Ellipsoid n} {u : Vec ℝ E.k} (hu : ‖u‖₂ ≤ 1) :
    E.q + E.G *ᵥ u ∈ E.construct := ⟨u, hu, rfl⟩

/-- Never empty, which is what the support function's maximum is attained at
when the direction is one `G` collapses. -/
theorem Ellipsoid.q_mem_construct (E : Ellipsoid n) : E.q ∈ E.construct :=
  ⟨0, by rw [norm₂_zero]; exact zero_le_one, by rw [Matrix.mulVec_zero, add_zero]⟩

end CORALean.Real
