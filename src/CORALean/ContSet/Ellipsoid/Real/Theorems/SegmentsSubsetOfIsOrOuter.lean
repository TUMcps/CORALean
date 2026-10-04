import CORALean.ContSet.Ellipsoid.Real.Operations.IsOrOuter
import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
import CORALean.ContSet.ContSet.ContSet

/-!
# Segments between two ellipsoids lie in an ellipsoid enclosing both

An ellipsoid is convex, so an ellipsoid containing both operands contains every segment between them
(`Ellipsoid.IsOrOuter`).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.segments_subset_of_isOrOuter {E₁ E₂ E : Ellipsoid n}
    (h : Ellipsoid.IsOrOuter E₁ E₂ E) : segments E₁.construct E₂.construct ⊆ E.construct := by
  rintro _ ⟨y₁, h₁, y₂, h₂, l, ⟨hl0, hl1⟩, rfl⟩
  exact E.convex_construct (h (Or.inl h₁)) (h (Or.inr h₂)) hl0 (by linarith) (by ring)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
