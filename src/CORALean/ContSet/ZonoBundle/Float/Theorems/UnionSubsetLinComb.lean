module

public import CORALean.ContSet.ContSet.Theorems.UnionSubsetSetLinComb
public import CORALean.ContSet.ZonoBundle.Float.Operations.LinComb
public import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.SetIntersection.Theorems.PairwiseOuter
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# A float bundle's `linComb` holds both operands, and their convex hull

As for a zonotope: the bundle is convex, so for two nonempty ones the segments are the convex hull
of the union and `SetIntersection.pairwise_outer` at `Zonotope.linComb_outer` puts that in the
result. Outer only; CORA's `convHull_` of a bundle goes through polytopes and is exact, which
this is not.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle

## Hypotheses
* `h₁` – first bundle nonempty
* `h₂` – second bundle nonempty

## Conclusion
* the union is contained in the result
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
  (union_subset_setLinComb h₁ h₂).trans (SetIntersection.pairwise_outer Set.linComb
    (fun _ _ _ _ => setLinComb_mono) fun p =>
      ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, Zonotope.linComb_outer _ _⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
