module

public import CORALean.ContSet.ConPolyZono.Real.Operations.IsFullDimCora
public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Theorems.IsFullDimRank

@[expose] public section

/-!
# Full dimension implies CORA's rank test

Dropping the constraints only enlarges the set, so an interior point of the constrained set is
one of the polynomial zonotope on the same generators, and `PolyZonotope.isFullDimCora_of_interior`
applies. The test is necessary and not sufficient.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.isFullDimCora_of_interior (cPZ : ConPolyZono α)
    (h : (interior cPZ.construct).Nonempty) : cPZ.isFullDimCora := by
  refine ⟨?_, PolyZonotope.isFullDimCora_of_interior cPZ.polyZonotope ?_⟩
  · obtain ⟨y, hy⟩ := h
    exact ⟨y, interior_subset hy⟩
  · exact h.mono (interior_mono cPZ.polyZonotope_contains)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
