module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsPinvQpinv

@[expose] public section

/-!
# The ellipsoid at any pseudo-inverse

The definition names one pseudo-inverse, `Ellipsoid.Qpinv`; any `P` meeting the four Penrose
conditions (`IsPinv`) describes the same set, `{x | (x - q)ᵀ P (x - q) ≤ 1, x - q ∈ range Q}`,
the four conditions determining `P` (`IsPinv.unique`). This is CORA's `pinv(Q)`, however it is
computed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's ellipsoid: `{x | (x - q)ᵀ Q⁺ (x - q) ≤ 1, x - q ∈ range Q}`, at any pseudo-inverse. -/
theorem Ellipsoid.construct_eq_pinv (E : Ellipsoid n) {P : Mat ℝ n n} (hP : IsPinv E.Q P) :
    E.construct = {x | (x - E.q) ⬝ᵥ P *ᵥ (x - E.q) ≤ 1 ∧ ∃ w, x - E.q = E.Q *ᵥ w} := by
  rw [hP.unique E.isPinv_Qpinv]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
