module

public import CORALean.Global.FrontierImageSubsetOfSingular
public import CORALean.Global.PathMeetsFrontier
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Order.Interval.Set.Pi

@[expose] public section

/-!
# A box missing the image of the boundary and of the singular points is in the range

[1, Thm. 3.1]: for `f : x → ℝⁿ` continuous on the box `x`, continuously differentiable in
`int x`, and a box `y`: (i) `y ∩ f(∂x) = ∅`, (ii) `y ∩ f(Σ) = ∅` with
`Σ = {x ∈ int x | det f'(x) = 0}`, (iii) `f(x₀) ∈ y` for some `x₀ ∈ x` (the paper's `x̃`, which
has no Lean identifier) give `y ⊆ f(x)`. The proof is the paper's: by [1, Lemma A.2]
(`frontier_image_subset_image_frontier_union_singular`) the box `y` misses the frontier of
`f(x)`, so it holds `f(x₀)` in the interior of the image; a point of `y` outside the image would
join it to `f(x₀)` by a path in `y` (the box is convex), which meets the frontier by
[1, Lemma A.1] (`path_meets_frontier`). The derivative is a strict one `f'` at the interior
points, which a continuous one gives.

## References

* [1] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued
      functions". Reliable Computing, 14:1-23, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3.1]: (i) `y ∩ f(∂x) = ∅`, (ii) `y ∩ f(Σ) = ∅` and (iii) `f(x₀) ∈ y` give
`y ⊆ f(x)`. -/
theorem Icc_subset_image_of_disjoint_boundary_singular
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {xlo xhi ylo yhi : Fin n → ℝ}
    (hf : ∀ x ∈ interior (Icc xlo xhi), HasStrictFDerivAt f (f' x) x)
    (hcont : ContinuousOn f (Icc xlo xhi))
    (hi : Disjoint (Icc ylo yhi) (f '' frontier (Icc xlo xhi)))
    (hii : Disjoint (Icc ylo yhi) (f '' {x | x ∈ interior (Icc xlo xhi) ∧
      LinearMap.det (f' x).toLinearMap = 0}))
    (hiii : ∃ x₀ ∈ Icc xlo xhi, f x₀ ∈ Icc ylo yhi) :
    Icc ylo yhi ⊆ f '' Icc xlo xhi := by -- --- PROOF ---
  have hE : IsCompact (f '' Icc xlo xhi) := isCompact_Icc.image_of_continuousOn hcont
  -- (1): `y` misses the frontier of the image
  have h1 : ∀ w ∈ Icc ylo yhi, w ∉ frontier (f '' Icc xlo xhi) := fun w hw hfr =>
    (frontier_image_subset_image_frontier_union_singular isCompact_Icc hf hcont hfr).elim
      (fun h => disjoint_left.mp hi hw h) (fun h => disjoint_left.mp hii hw h)
  obtain ⟨x₀, hx₀, hy⟩ := hiii
  -- hence `f(x₀)` is an interior point of the image
  have hint : f x₀ ∈ interior (f '' Icc xlo xhi) := by
    by_contra hni
    exact h1 _ hy ⟨subset_closure ⟨x₀, hx₀, rfl⟩, hni⟩
  intro z hz
  by_contra hzE
  -- the segment from `f(x₀)` to `z` stays in the box `y`
  let w : ℝ → (Fin n → ℝ) := fun t => f x₀ + t • (z - f x₀)
  have hw : ContinuousOn w (Icc 0 1) := (by fun_prop : Continuous w).continuousOn
  have hwy : ∀ t ∈ Icc (0 : ℝ) 1, w t ∈ Icc ylo yhi := fun t ht =>
    (convex_Icc ylo yhi).add_smul_sub_mem hy hz ht
  obtain ⟨t, ht, hwt⟩ := path_meets_frontier hE.isClosed hw (by simpa [w] using hint)
    (by simpa [w] using hzE)
  exact h1 _ (hwy t ht) hwt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
