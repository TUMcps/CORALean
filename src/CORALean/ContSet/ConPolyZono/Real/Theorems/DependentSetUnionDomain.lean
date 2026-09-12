import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# The dependent generator map splits over a union of factor domains

The result is [1, Lemma 2], a prerequisite for the union construction of
[1, Thm. 1] — not itself formalized here, since its other prerequisite,
[1, Prop. 14] (Appendix A, `subset`), is real work of its own: an expansion of
one exponent column into as many as `E(r,i)+1` new ones, built from a binomial
identity rather than from a block-diagonal layout like every other operation
in this file's directory.

[1] states the domains `D₁, D₂` as subsets of the unit cube `[-1,1]ᵖ`; nothing
in the proof reads that, so it is dropped here and the result specializes to
[1]'s at that restriction. The proof is `Set.image_union`'s content, unfolded
to the paper's set-builder notation rather than phrased through `Set.image`
itself, since neither side names the underlying map on its own.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.dependentSet_union_domain {p h : ℕ} (c : α) (G : Fin h → α)
    (E : Fin p → Fin h → ℕ) (D₁ D₂ : Set (Fin p → ℝ)) :
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
