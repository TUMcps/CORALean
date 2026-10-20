module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# The dependent generator map splits over a union of factor domains

The result is [1, Lemma 2], the step Appendix A takes once A.1 has cut the factor domain of the
union in [1, Thm. 1] in two: a dependent generator map sends a union of domains to the union of
its images.

[1] states the domains `D₁, D₂` as subsets of the unit cube `[-1,1]ᵖ`; nothing in the proof reads
that, so it is dropped here. The proof is `Set.image_union`'s content in the paper's set-builder
notation. `union_exact_of_noZeroCol` does not go through this statement but through
`union_domain_iff`.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `c` – center
* `G` – generators
* `E` – exponent matrix
* `D₁` – first factor domain
* `D₂` – second factor domain

## Hypotheses
* none

## Conclusion
* the generator image of a union is the union of the images

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.dependentSet_union_domain {p h : ℕ} (c : α) (G : Fin h → α)
    (E : Fin p → Fin h → ℕ) (D₁ D₂ : Set (Fin p → ℝ)) : -- --- CONCL ---
    {x | ∃ a ∈ D₁ ∪ D₂, x = c + ∑ i, PolyZonotope.monomial E a i • G i}
      = {x | ∃ a ∈ D₁, x = c + ∑ i, PolyZonotope.monomial E a i • G i}
        ∪ {x | ∃ a ∈ D₂, x = c + ∑ i, PolyZonotope.monomial E a i • G i} := by -- --- PROOF ---
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha | ha, rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a, Or.inl ha, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
