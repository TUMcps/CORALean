import CORALean.ContSet.ContSet.Theorems.DependencyPreservingComp
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapSubsetAt

/-!
# Dependency preservation, witnessed

What this records is that [1, Def. 4] is a property an operation in this tree actually has, and not
only a shape: `map` instantiates it at the factor sub-boxes `subsetAt` reads, and `map_subsetAt` is
the whole proof, the equality it states giving the inclusion [1, Def. 4] asks for and the reverse
besides. One sub-box serves both ends because `map` leaves the factor count alone, so the two
evaluation functions share a domain and no `Fin.cast` appears; an operation that repacked the
factors would need one. The second example is [1, Lemma 2] at a pair of maps: `Set.monotone_image`
is the monotonicity it asks of the outer operation, and nothing else is supplied.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

-- Anonymous, since their content is that they elaborate.

/-- `map` preserves dependencies for the image under `f`: one sub-box `B` names
corresponding subsets before and after it. -/
example {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) :
    DependencyPreserving (Set.image f) pZ.subsetAt (pZ.map f).subsetAt :=
  fun B => (PolyZonotope.map_subsetAt f pZ B).symm.subset

/-- Two maps in a row, through [1, Lemma 2]: the composed image is preserved
along the chain they build. -/
example {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    [AddCommGroup γ] [Module ℝ γ] (f : α →ₗ[ℝ] β) (g : β →ₗ[ℝ] γ) (pZ : PolyZonotope α) :
    DependencyPreserving (Set.image g ∘ Set.image f) pZ.subsetAt ((pZ.map f).map g).subsetAt :=
  DependencyPreserving.comp Set.monotone_image
    (fun B => (PolyZonotope.map_subsetAt f pZ B).symm.subset)
    (fun B => (PolyZonotope.map_subsetAt g (pZ.map f) B).symm.subset)

end CORALean.Real
