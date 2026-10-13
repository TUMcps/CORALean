module

public import CORALean.ContSet.ContSet.Theorems.UnionSubsetSegments
public import CORALean.ContSet.ZonoBundle.Float.Theorems.Convex
public import CORALean.ContSet.ZonoBundle.Float.Theorems.LinCombOuter

@[expose] public section

/-!
# A float bundle's `linComb` holds both operands, and their convex hull

As for a zonotope: the bundle is convex, so for two nonempty ones the segments are the convex hull
of the union and `linComb_outer` puts that in the result. Outer only; CORA's `convHull_` of a bundle
goes through polytopes and is exact, which this is not.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `or`: the union of two nonempty float zonotope bundles lies in their `linComb`. -/
theorem ZonoBundle.union_subset_linComb (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n))
    (h₁ : zB₁.construct.Nonempty) (h₂ : zB₂.construct.Nonempty) :
    zB₁.construct ∪ zB₂.construct ⊆ (zB₁.linComb zB₂).construct :=
  (union_subset_segments h₁ h₂).trans (ZonoBundle.linComb_outer zB₁ zB₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
