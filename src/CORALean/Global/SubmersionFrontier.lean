import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Compactness.Compact

/-!
# A submersion maps no interior point onto the frontier of its image

[1, Lemma 3.1]: for `f₁:ᵣ` with a Jacobian of rank `r` everywhere, as (3) gives it, and `E`
compact, `∂(f₁:ᵣ(E)) ⊆ f₁:ᵣ(∂E)`. A submersion is an open map at every point where it is
one: `HasStrictFDerivAt.map_nhds_eq_of_surj` is the local surjectivity theorem behind it.
Stated for any `g` with a strict, surjective derivative at the interior points of `E`, which
is all the proof uses; (3) gives it at every point of `D ⊇ E`.

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

open Set Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 3.1]: `∂(g(E)) ⊆ g(∂E)` for `E` compact and `g` a submersion inside `E`. -/
theorem frontier_image_subset_image_frontier {g : E → F} {g' : E → E →L[ℝ] F} {K : Set E}
    (hK : IsCompact K) (hg : ∀ x ∈ interior K, HasStrictFDerivAt g (g' x) x)
    (hsurj : ∀ x ∈ interior K, (g' x).range = ⊤) (hcont : ContinuousOn g K) :
    frontier (g '' K) ⊆ g '' frontier K := by -- --- PROOF ---
  intro y hy
  -- the image is compact, hence closed, so its frontier lies in it
  obtain ⟨x, hx, rfl⟩ := (hK.image_of_continuousOn hcont).isClosed.frontier_subset hy
  refine ⟨x, ?_, rfl⟩
  rw [hK.isClosed.frontier_eq]
  refine ⟨hx, fun hint => hy.2 (mem_interior_iff_mem_nhds.mpr ?_)⟩
  -- at an interior point `g` maps neighbourhoods onto neighbourhoods
  rw [← (hg x hint).map_nhds_eq_of_surj (hsurj x hint)]
  exact image_mem_map (mem_interior_iff_mem_nhds.mp hint)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
