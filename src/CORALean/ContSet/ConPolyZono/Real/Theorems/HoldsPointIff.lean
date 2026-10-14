module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# `ConPolyZono.holds_point_iff`

At a degenerate `b`, `holds` collapses to the paper's equality [1]: the point
case that reads a plain equation as `holds` with zero slack.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The paper's equality, as the degenerate interval. -/
theorem ConPolyZono.holds_point_iff {p m q : ℕ} (A : Mat ℝ m q) (b : Vec ℝ m)
    (R : Fin p → Fin q → ℕ) (a : Fin p → ℝ) :
    ConPolyZono.holds A (Interval.point b) R a
      ↔ ∀ i, (A *ᵥ PolyZonotope.monomial R a) i = b i :=
  forall_congr' fun _ => ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
