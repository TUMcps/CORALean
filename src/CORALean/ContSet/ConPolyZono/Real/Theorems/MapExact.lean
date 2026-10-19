module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.map` is exactly the image under a linear map

The same factors and independent coefficients work in both directions, and the
constraint is the same proposition about them before and after — a linear map of
the ambient space moves points, not factors. Linearity carried through the two
sums is then the whole proof.

`MtimesExact` is this at `A *ᵥ ·`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.map_exact (f : α →ₗ[ℝ] β) (cPZ : ConPolyZono α) :
    f '' cPZ.construct = (cPZ.map f).construct := by -- --- PROOF ---
  have hf : ∀ (a : Fin cPZ.p → ℝ) (b : Fin cPZ.qI → ℝ),
      f (cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i + ∑ j, b j • cPZ.GI j)
        = (cPZ.map f).c + ∑ i, PolyZonotope.monomial (cPZ.map f).E a i • (cPZ.map f).G i
            + ∑ j, b j • (cPZ.map f).GI j := by
    intro a b
    rw [map_add, map_add, map_sum, map_sum]
    congr 1
    · exact congrArg _ (Finset.sum_congr rfl fun i _ => map_smul f _ (cPZ.G i))
    · exact Finset.sum_congr rfl fun j _ => map_smul f (b j) (cPZ.GI j)
  -- both inclusions are `hf` read in the two directions; the constraint never moves
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨a, b, ha, hb, hsat, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, hsat, hf a b⟩
  · rintro y ⟨a, b, ha, hb, hsat, hy⟩
    refine ⟨cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i + ∑ j, b j • cPZ.GI j,
      ⟨a, b, ha, hb, hsat, rfl⟩, ?_⟩
    rw [hy]
    exact hf a b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
