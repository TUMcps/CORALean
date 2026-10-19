module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IsOrOuter
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Segments between two ellipsoids lie in an ellipsoid enclosing both

An ellipsoid is convex, so an ellipsoid containing both operands contains every segment between them
(`Ellipsoid.IsOrOuter`).

## Inputs
* `E₁` – first ellipsoid
* `E₂` – second ellipsoid
* `E` – candidate hull

## Hypotheses
* `h` – `E` contains both operands

## Conclusion
* the segments between `E₁` and `E₂` lie in `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.setLinComb_subset_of_isOrOuter {E₁ E₂ E : Ellipsoid n}
    (h : Ellipsoid.IsOrOuter E₁ E₂ E) : Set.linComb E₁.construct E₂.construct ⊆ E.construct := by
  rintro _ ⟨y₁, h₁, y₂, h₂, l, ⟨hl0, hl1⟩, rfl⟩
  exact E.convex_construct (h (Or.inl h₁)) (h (Or.inr h₂)) hl0 (by linarith) (by ring)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
