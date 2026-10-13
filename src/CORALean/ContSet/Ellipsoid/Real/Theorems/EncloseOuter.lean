module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Enclose
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.SegmentsSubsetOfIsOrOuter

@[expose] public section

/-!
# `Ellipsoid.enclose` encloses the hull of `E` and `M Eplus`

Outer, and of the set the code computes, `M Eplus`: not of the documented `M E ⊕ Eplus`, which it
misses (`Ellipsoid.enclose_cora_counterexample`). The enclosure is of the segments between the
operands, the convex hull since both are convex; it rests on the hull `orOA` enclosing both operands
(`Ellipsoid.IsOrOuter`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.enclose_outer (orOA : Ellipsoid n → Ellipsoid n → Ellipsoid n)
    (hor : ∀ E₁ E₂, Ellipsoid.IsOrOuter E₁ E₂ (orOA E₁ E₂))
    (E : Ellipsoid n) (M : Mat ℝ n m) (Eplus : Ellipsoid m) :
    segments E.construct ((M *ᵥ ·) '' Eplus.construct) ⊆
      (Ellipsoid.enclose orOA E M Eplus).construct := by
  rw [Ellipsoid.mtimes_exact]
  exact Ellipsoid.segments_subset_of_isOrOuter (hor _ _)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
