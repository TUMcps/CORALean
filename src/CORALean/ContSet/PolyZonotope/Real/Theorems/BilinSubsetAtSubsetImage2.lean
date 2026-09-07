import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinSubsetAt

/-!
# `bilin`'s subset at `B` sits inside the pairwise image

The containment half of the gap `bilin_subsetAt` documents: every point the
diagonal image reaches is also reached by pairing some point of `pZ₁.subsetAt B`
with some point of `pZ₂`'s subset at the reindexed box — namely the same shared
factor vector, read through each set's own point. The reverse containment need
not hold, and generally does not: a pairwise `image2` also reaches every
combination of an `pZ₁`-point at one factor vector with an `pZ₂`-point at an
unrelated one, which no shared factor vector names. That gap is [1]'s whole
point, and is not proved strict here — only crossed one way.

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

/-- The diagonal subset `bilin` reaches at `B` is contained in the pairwise
`image2` of `f` over the two sets' own subsets at `B`. -/
theorem PolyZonotope.bilin_subsetAt_subset_image2 (f : α →ₗ[ℝ] β →ₗ[ℝ] γ)
    (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) (hp : pZ₁.p = pZ₂.p)
    (B : Set (Fin pZ₁.p → ℝ)) :
    (pZ₁.bilin f pZ₂ hp).subsetAt B
      ⊆ Set.image2 (fun x y => f x y) (pZ₁.subsetAt B)
          (pZ₂.subsetAt ((fun a k => a (Fin.cast hp.symm k)) '' B)) := by
  rw [PolyZonotope.bilin_subsetAt]
  rintro _ ⟨a, ha, rfl⟩
  exact Set.mem_image2_of_mem ⟨a, ha, rfl⟩ ⟨fun k => a (Fin.cast hp.symm k), ⟨a, ha, rfl⟩, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
