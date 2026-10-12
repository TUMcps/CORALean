import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Compactness.Compact

/-!
# The frontier of the image lies in the image of the boundary and of the singular points

[1, Lemma A.2]: for `E ⊆ ℝⁿ` compact, `f : E → ℝⁿ` continuous and continuously differentiable
in `int E`, and `Σ = {x ∈ int E | det f'(x) = 0}`, `∂(f(E)) ⊆ f(∂E) ∪ f(Σ)`. The proof is the
paper's: the image is compact, so a frontier point is `f(x)`; at an interior `x` with
`det f'(x) ≠ 0` the inverse function theorem makes `f` open at `x`, which puts `f(x)` in the
interior of the image. Stated for a strict derivative `g'` at the interior points, which a
continuous one gives.

## References

* [1] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued
      functions". Reliable Computing, 14:1-23, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Filter Topology

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma A.2]: `∂(f(E)) ⊆ f(∂E) ∪ f(Σ)`, `Σ` the interior points with `det f' = 0`. -/
theorem frontier_image_subset_image_frontier_union_singular
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hf : ∀ x ∈ interior K, HasStrictFDerivAt f (f' x) x)
    (hcont : ContinuousOn f K) :
    frontier (f '' K) ⊆ f '' frontier K ∪
      f '' {x | x ∈ interior K ∧ LinearMap.det (f' x).toLinearMap = 0} := by -- --- PROOF ---
  intro y hy
  -- the image is compact, hence closed, so its frontier lies in it
  obtain ⟨x, hx, rfl⟩ := (hK.image_of_continuousOn hcont).isClosed.frontier_subset hy
  by_cases hxint : x ∈ interior K
  · right
    refine ⟨x, ⟨hxint, ?_⟩, rfl⟩
    by_contra hdet
    -- `det f'(x) ≠ 0` makes `f'(x)` onto
    have hinj : Function.Injective (f' x).toLinearMap :=
      LinearMap.ker_eq_bot.mp (by
        by_contra hker
        exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker))
    have hsurj : (f' x).range = ⊤ :=
      LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hinj)
    -- so `f` is open at `x`, and `f(x)` is an interior point of the image
    refine hy.2 (mem_interior_iff_mem_nhds.mpr ?_)
    rw [← (hf x hxint).map_nhds_eq_of_surj hsurj]
    exact image_mem_map (mem_interior_iff_mem_nhds.mp hxint)
  · left
    exact ⟨x, by rw [hK.isClosed.frontier_eq]; exact ⟨hx, hxint⟩, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
