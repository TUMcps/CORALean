module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `plus` grows with both operands

`plus` is exact, so what it denotes is the Minkowski sum of what its operands
do, and a Minkowski sum is monotone in each side. Stated because an algorithm
built out of `plus` needs it once per layer, and `plus_exact` read twice is not
what a proof of monotonicity should look like at every one of them.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A larger pair of operands denotes a larger sum. -/
theorem PolyZonotope.plus_mono {pZ₁ pZ₂ qZ₁ qZ₂ : PolyZonotope α}
    (h₁ : pZ₁.construct ⊆ pZ₂.construct) (h₂ : qZ₁.construct ⊆ qZ₂.construct) :
    (pZ₁.plus qZ₁).construct ⊆ (pZ₂.plus qZ₂).construct := by
  rw [← PolyZonotope.plus_exact, ← PolyZonotope.plus_exact]
  exact Set.add_subset_add h₁ h₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
