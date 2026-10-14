module

public import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSegments
public import CORALean.ContSet.ConZonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Theorems.Convex

@[expose] public section

/-!
# A float constrained zonotope's `linComb` holds both operands, and their convex hull

As for a zonotope: what a float constrained zonotope denotes is a nominal one plus an error box,
both convex, so for two nonempty ones the segments are the convex hull of the union and
`linComb_outer` puts that in the result. Outer only at float; the exact layer's
`ConZonotope.linComb_eq_convexHull` says the hull is all there is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `convHull_`: the convex hull of the union of two nonempty float constrained zonotopes lies in
their `linComb`. -/
theorem ConZonotope.convexHull_subset_linComb (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n))
    (h₁ : cZ₁.construct.Nonempty) (h₂ : cZ₂.construct.Nonempty) :
    convexHull ℝ (cZ₁.construct ∪ cZ₂.construct) ⊆ (cZ₁.linComb cZ₂).construct := by
  have hc : ∀ c : ConZonotope 𝕋 (Vec 𝕋 n), Convex ℝ c.construct := fun c =>
    Convex.add (nominal c).convex_construct c.I_error.nominal.convex_construct
  rw [convexHull_union_eq_segments h₁ h₂ (hc cZ₁) (hc cZ₂)]
  exact ConZonotope.linComb_outer cZ₁ cZ₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
