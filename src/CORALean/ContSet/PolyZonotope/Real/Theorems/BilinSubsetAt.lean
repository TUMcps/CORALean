module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint

@[expose] public section

/-!
# `bilin`'s subset at `B` is the diagonal image, not a pairwise one

`bilin_point` composed: the subset `B` reaches under `bilin f pZ₁ pZ₂ hp` is the
image of `B` under `a ↦ f (pZ₁.point a) (pZ₂.point (a ∘ Fin.cast hp.symm))`, one
factor vector driving both points at once — *not*
`Set.image2 f (pZ₁.subsetAt B) (pZ₂.subsetAt _)`, which lets the two points range
independently. `bilin_subsetAt_subset_image2` proves the diagonal is contained
in that pairwise image and is generally strictly smaller: the gap is [1, Def. 4]'s
whole point, what a dependency-preserving representation buys over one that
can only pair sets.

## Inputs
* `f` – bilinear map
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `B` – box of factor values

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* subset at the box is the diagonal image

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `bilin`'s subset at `B` is `f` at the two points, ranged over one shared
factor vector — the diagonal image, not the pairwise one. -/
theorem PolyZonotope.bilin_subsetAt (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α)
    (pZ₂ : PolyZonotope β) (hp : pZ₁.p = pZ₂.p) (B : Set (Fin pZ₁.p → ℝ)) :
    (pZ₁.bilin f pZ₂ hp).subsetAt B
      = (fun a => f (pZ₁.point a) (pZ₂.point fun k => a (Fin.cast hp.symm k))) '' B := by
  show (pZ₁.bilin f pZ₂ hp).point '' B = _
  exact Set.image_congr fun a _ => PolyZonotope.bilin_point f pZ₁ pZ₂ hp a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
