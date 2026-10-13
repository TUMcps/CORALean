module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.holds_congr`

The constraint reads its data only through the vector `A μ(α)`: any rewrite
that leaves that vector alone leaves `holds` alone, which is what lets
`compact` rewrite the constraint block.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- A rewriting of the constraint block that leaves `A μ(α)` alone leaves the
constraint alone — which is what compacting `A` and `EC` does. -/
theorem ConPolyZono.holds_congr {p p' m s s' : ℕ} {A : Mat ℝ m s} {A' : Mat ℝ m s'}
    {b : Interval (Vec ℝ m)} {EC : Fin p → Fin s → ℕ} {EC' : Fin p' → Fin s' → ℕ}
    {a : Fin p → ℝ} {a' : Fin p' → ℝ}
    (h : A' *ᵥ PolyZonotope.monomial EC' a' = A *ᵥ PolyZonotope.monomial EC a) :
    ConPolyZono.holds A b EC a ↔ ConPolyZono.holds A' b EC' a' := by
  rw [ConPolyZono.holds, ConPolyZono.holds, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
