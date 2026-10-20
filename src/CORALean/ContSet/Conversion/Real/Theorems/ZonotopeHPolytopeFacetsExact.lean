module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeHPolytopeFacetsContains
public import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalCompPermAbs
public import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalEqZeroOfNotInjective
public import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# CORA's facet polytope is the zonotope, for generators that span

[1, Thm. 2] (`Zonotope.hRep_eq`) states the zonotope by the cross products of every `n - 1`-tuple
of generators; CORA takes one combination per set of generators. A tuple with a repeat has the
zero normal (`facetNormal_eq_zero_of_not_injective`); one without is a combination, its sorted
image, permuted, and a permutation changes the normal by a sign only
(`abs_dot_facetNormal_comp_perm`). Dividing a nonzero normal by its length scales both sides of
its bound by the same positive number.

## Inputs
* `Z` – zonotope

## Hypotheses
* `hspan` – generators span the space

## Conclusion
* facet polytope equals the zonotope

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every tuple's normal is `0`, or one of CORA's combination normals up to a sign. -/
private theorem aux_tuple_normal (Z : Zonotope (Vec ℝ (m + 1)))
    (S : Fin m → Fin Z.h) : -- --- CONCL ---
    Z.facetNormal S = 0 ∨
      ∃ v ∈ Z.facetNormals, ∀ y, |y ⬝ᵥ Z.facetNormal S| = |y ⬝ᵥ v| := by -- --- PROOF ---
  by_cases hS : Function.Injective S
  swap
  · exact Or.inl (Z.facetNormal_eq_zero_of_not_injective S hS)
  right
  -- the sorted image of `S` is a combination
  set l : List (Fin Z.h) := (Finset.univ.image S).sort (· ≤ ·) with hl
  have hlen : l.length = m := by
    rw [hl, Finset.length_sort, Finset.card_image_of_injective _ hS, Finset.card_univ,
      Fintype.card_fin]
  have hmem : l ∈ (List.finRange Z.h).sublistsLen m := by
    refine List.mem_sublistsLen.mpr ⟨?_, hlen⟩
    exact List.sublist_of_subperm_of_pairwise
      ((Finset.sort_nodup _ _).subperm fun a _ => List.mem_finRange a)
      (Finset.pairwise_sort _ _) ((List.pairwise_lt_finRange _).imp le_of_lt)
  -- `S` is that combination after a permutation of its positions
  have hin : ∀ j, S j ∈ l := fun j => (Finset.mem_sort _).mpr (Finset.mem_image_of_mem S
    (Finset.mem_univ j))
  set T : Fin m → Fin Z.h := fun j => l.get ⟨j, lt_of_lt_of_eq j.isLt hlen.symm⟩ with hT
  let f : Fin m → Fin m := fun j =>
    ⟨l.idxOf (S j), lt_of_lt_of_eq (List.idxOf_lt_length_of_mem (hin j)) hlen⟩
  have hTf : ∀ j, T (f j) = S j := fun j => List.getElem_idxOf _
  have hf : Function.Injective f := fun a b hab => hS (by rw [← hTf a, ← hTf b, hab])
  set σ : Equiv.Perm (Fin m) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hTσ : T ∘ σ = S := funext hTf
  refine ⟨Z.facetNormal T, List.mem_map.mpr ⟨⟨l, hmem⟩, List.mem_attach _ _, rfl⟩, fun y => ?_⟩
  rw [← hTσ]
  exact Z.abs_dot_facetNormal_comp_perm T σ y

/-- Scaling a row by a positive number scales both sides of its bound. -/
private theorem aux_scale_iff {a : ℝ} (ha : 0 < a) (v x : Vec ℝ (m + 1)) {h : ℕ}
    (G : Fin h → Vec ℝ (m + 1)) :
    |(a • v) ⬝ᵥ x| ≤ ∑ j, |(a • v) ⬝ᵥ G j| ↔ |v ⬝ᵥ x| ≤ ∑ j, |v ⬝ᵥ G j| := by
  simp only [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_pos ha, ← Finset.mul_sum]
  exact mul_le_mul_iff_of_pos_left ha


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `polytope(Z)` rows describe the zonotope exactly when its generators span. -/
theorem Zonotope.hPolytopeFacets_exact (Z : Zonotope (Vec ℝ (m + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) : -- --- CONCL ---
    Z.hPolytopeFacets.construct = Z.construct := by -- --- PROOF ---
  -- spanning generators are not all zero
  have hG : ¬∀ j, Z.G j = 0 := by
    intro h
    have hsub : Set.range Z.G ⊆ {0} := by
      rintro _ ⟨j, rfl⟩
      exact h j
    have hbot := Submodule.span_mono (R := ℝ) hsub
    rw [hspan, Submodule.span_singleton_eq_bot.mpr rfl, top_le_iff] at hbot
    have h1 : (Pi.single 0 1 : Vec ℝ (m + 1)) ∈ (⊥ : Submodule ℝ (Vec ℝ (m + 1))) := by
      rw [hbot]; exact Submodule.mem_top
    have := congrFun ((Submodule.mem_bot ℝ).mp h1) 0
    simp at this
  refine subset_antisymm (fun x hx => ?_) Z.hPolytopeFacets_contains
  rw [Z.mem_hPolytopeFacets_iff hG] at hx
  rw [Z.hRep_eq hspan]
  intro S
  -- each tuple's bound is a row's, or trivial
  rcases aux_tuple_normal Z S with h0 | ⟨v, hv, hsign⟩
  · rw [h0]
    simp only [zero_dotProduct, abs_zero, Finset.sum_const_zero, le_refl]
  · have hS : ∀ y, |Z.facetNormal S ⬝ᵥ y| = |v ⬝ᵥ y| := fun y => by
      rw [dotProduct_comm, hsign y, dotProduct_comm]
    rw [hS, Finset.sum_congr rfl fun j _ => hS (Z.G j)]
    by_cases hv0 : v = 0
    · simp only [hv0, zero_dotProduct, abs_zero, Finset.sum_const_zero, le_refl]
    -- the row `v / ‖v‖₂` is one of CORA's, and its bound is `v`'s scaled
    have hpos : 0 < (‖v‖₂)⁻¹ := by
      refine inv_pos.mpr (lt_of_le_of_ne (norm₂_nonneg v) fun h => hv0 ?_)
      rw [← norm_toEuclidean] at h
      exact (map_eq_zero_iff _ toEuclidean.injective).mp (norm_eq_zero.mp h.symm)
    have hrow : (‖v‖₂)⁻¹ • v ∈ Z.facetRows :=
      List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hv, by simpa using hv0⟩, rfl⟩
    exact (aux_scale_iff hpos v _ Z.G).mp (hx _ hrow)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
