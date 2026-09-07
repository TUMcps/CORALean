import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint

/-!
# `bilin`'s subset at `B` is the diagonal image, not a pairwise one

`bilin_point` composed: the subset `B` reaches under `bilin f S₁ S₂ hp` is the
image of `B` under `a ↦ f (S₁.point a) (S₂.point (a ∘ Fin.cast hp.symm))`, one
factor vector driving both points at once — *not*
`Set.image2 f (S₁.subsetAt B) (S₂.subsetAt _)`, which lets the two points range
independently. `bilin_subsetAt_subset_image2` proves the diagonal is contained
in that pairwise image and is generally strictly smaller: the gap is [1]'s
whole point, what a dependency-preserving representation buys over one that
can only pair sets.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `bilin`'s subset at `B` is `f` at the two points, ranged over one shared
factor vector — the diagonal image, not the pairwise one. -/
theorem PolyZonotope.bilin_subsetAt (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (S₁ : PolyZonotope α)
    (S₂ : PolyZonotope β) (hp : S₁.p = S₂.p) (B : Set (Fin S₁.p → ℝ)) :
    (S₁.bilin f S₂ hp).subsetAt B
      = (fun a => f (S₁.point a) (S₂.point fun k => a (Fin.cast hp.symm k))) '' B := by
  show (S₁.bilin f S₂ hp).point '' B = _
  exact Set.image_congr fun a _ => PolyZonotope.bilin_point f S₁ S₂ hp a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
