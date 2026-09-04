import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# `Ellipsoid.q_mem_construct`

`mem_construct` at `u = 0`, the centre — what makes the representation never
empty, and where the support function's maximum is attained when the
direction is one `G` collapses.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- Never empty, which is what the support function's maximum is attained at
when the direction is one `G` collapses. -/
theorem Ellipsoid.q_mem_construct (E : Ellipsoid n) : E.q ∈ E.construct :=
  ⟨0, by rw [norm₂_zero]; exact zero_le_one, by rw [Matrix.mulVec_zero, add_zero]⟩

end CORALean.Real
