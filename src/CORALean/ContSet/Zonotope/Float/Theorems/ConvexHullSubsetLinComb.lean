import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSegments
import CORALean.ContSet.Zonotope.Float.Theorems.Convex
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter

/-!
# A float zonotope's `linComb` holds both operands, and their convex hull

What the float `or` and `convHull_` of a zonotope are: `linComb` is the enclosure CORA's
`enclose` makes, and a zonotope is convex, so the segments between two nonempty ones are the
convex hull of their union (`convexHull_union_eq_segments`) and `linComb_outer` puts that in the
result. Outer only: the zonotope `linComb` is coarser than the hull.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `convHull_`: the convex hull of the union of two nonempty float zonotopes lies in their
`linComb`. -/
theorem Zonotope.convexHull_subset_linComb (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (h₁ : Z₁.construct.Nonempty)
    (h₂ : Z₂.construct.Nonempty) :
    convexHull ℝ (Z₁.construct ∪ Z₂.construct) ⊆ (Z₁.linComb Z₂).construct := by
  rw [convexHull_union_eq_segments h₁ h₂ Z₁.convex_construct Z₂.convex_construct]
  exact Zonotope.linComb_outer Z₁ Z₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
