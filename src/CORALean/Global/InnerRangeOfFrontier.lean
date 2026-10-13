module

public import CORALean.Global.SubmersionFrontier
public import Mathlib.Topology.Connected.Basic

@[expose] public section

/-!
# A connected set the frontier's image misses is inside the image

[1, Thm. 3.1]: `f₁:ᵣ` a submersion on `u`, `y₁ ∩ f₁:ᵣ(∂u) = ∅` (i) and `f₁:ᵣ(ũ) ∈ y₁` for some
`ũ ∈ u` (ii) give `y₁ ⊆ f₁:ᵣ(u)`. The proof is the paper's: by [1, Lemma 3.1]
(`frontier_image_subset_image_frontier`) `y₁` misses the frontier of `f₁:ᵣ(u)`, so a
connected `y₁` meeting its interior stays inside it. Boxes `u` and `y₁` are the case the paper
states; compact and preconnected is all that is used.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3.1]: (i) `y ∩ g(∂u) = ∅` and (ii) `g(ũ) ∈ y`, `ũ ∈ u`, give `y ⊆ g(u)`. -/
theorem subset_image_of_disjoint_image_frontier {g : E → F} {g' : E → E →L[ℝ] F} {u : Set E}
    (hu : IsCompact u) (hg : ∀ x ∈ interior u, HasStrictFDerivAt g (g' x) x)
    (hsurj : ∀ x ∈ interior u, (g' x).range = ⊤) (hcont : ContinuousOn g u) {y : Set F}
    (hy : IsPreconnected y) (hi : Disjoint y (g '' frontier u)) (hii : ∃ ũ ∈ u, g ũ ∈ y) :
    y ⊆ g '' u := by -- --- PROOF ---
  have hKc : IsClosed (g '' u) := (hu.image_of_continuousOn hcont).isClosed
  have hfr := frontier_image_subset_image_frontier hu hg hsurj hcont
  -- a point of `y` in the image is an interior point of it, by (i) and Lemma 3.1
  have hint : ∀ w ∈ y, w ∈ g '' u → w ∈ interior (g '' u) := fun w hw hwK => by
    by_contra hni
    exact disjoint_left.mp hi hw (hfr ⟨subset_closure hwK, hni⟩)
  obtain ⟨ũ, hũ, hgy⟩ := hii
  have hsub : y ⊆ interior (g '' u) :=
    hy.subset_of_closure_inter_subset isOpen_interior ⟨g ũ, hgy, hint _ hgy ⟨ũ, hũ, rfl⟩⟩
      fun w hw => hint w hw.2 (hKc.closure_eq ▸ closure_mono interior_subset hw.1)
  exact fun w hw => interior_subset (hsub hw)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
