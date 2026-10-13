module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Enclose2
public import CORALean.ContSet.Ellipsoid.Real.Theorems.SegmentsSubsetOfIsOrOuter

@[expose] public section

/-!
# `Ellipsoid.enclose₂` encloses the hull of `E` and `E2`

Outer, given the hull `orOA` encloses both operands (`Ellipsoid.IsOrOuter`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.enclose₂_outer (orOA : Ellipsoid n → Ellipsoid n → Ellipsoid n)
    (hor : ∀ E₁ E₂, Ellipsoid.IsOrOuter E₁ E₂ (orOA E₁ E₂)) (E E2 : Ellipsoid n) :
    segments E.construct E2.construct ⊆ (Ellipsoid.enclose₂ orOA E E2).construct :=
  Ellipsoid.segments_subset_of_isOrOuter (hor _ _)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
