import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter

/-!
# A perturbed image, inner-approximated by cancellation

`f '' X` minus a set `B` covering `f x - g x` on `X` lies inside `g '' X`,
provided `g '' X` is convex and closed and `B` is nonempty and bounded. Each
`f x` is `g x + (f x - g x)`, so `f '' X ⊆ g '' X + B`, and
`minkowskiDiff_inner_of_outer` cancels `B` by Rådström's law.

No smallness and no invertibility: at `f = Ē`, `g = E` matrices and `X` a
zonotope, the perturbation `E - Ē` may be as large as it likes, only `B` has to
cover it. Convexity of `g '' X` is what does the work; without it the statement
needs a contraction (`minkowskiDiff_image_subset_image_of_contracting`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {α β : Type} [NormedAddCommGroup β] [NormedSpace ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `f '' X ⊖ B ⊆ g '' X` when `B` is nonempty, bounded and covers `f x - g x` on `X`, and
`g '' X` is convex and closed. -/
theorem minkowskiDiff_image_subset_image_of_convex (f g : α → β) {X : Set α} {B : Set β}
    (hB : B.Nonempty) (hBb : Bornology.IsBounded B) (hconv : Convex ℝ (g '' X))
    (hcl : IsClosed (g '' X)) (hfg : ∀ x ∈ X, f x - g x ∈ B) :
    minkowskiDiff (f '' X) B ⊆ g '' X := by
  refine minkowskiDiff_inner_of_outer hB hBb hconv hcl ?_
  -- `f x = g x + (f x - g x)`
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨g x, ⟨x, hx, rfl⟩, f x - g x, hfg x hx, add_sub_cancel _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
