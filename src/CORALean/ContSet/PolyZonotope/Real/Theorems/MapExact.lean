module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.Map

@[expose] public section

/-!
# `PolyZonotope.map` is exactly the image under a linear map

The same factors and independent coefficients work in both directions — a linear
map introduces no freedom and removes none — so linearity carried through the
two sums is the whole proof. The monomials are untouched because they are
scalars, which is why the exponent matrix never enters.

`MtimesExact` is this at `A *ᵥ ·`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.map_exact (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) :
    f '' pZ.construct = (pZ.map f).construct := by -- --- PROOF ---
  have hf : ∀ (a : Fin pZ.p → ℝ) (b : Fin pZ.q → ℝ),
      f (pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, b j • pZ.GI j)
        = (pZ.map f).c + ∑ i, PolyZonotope.monomial (pZ.map f).E a i • (pZ.map f).G i
            + ∑ j, b j • (pZ.map f).GI j := by
    intro a b
    rw [map_add, map_add, map_sum, map_sum]
    congr 1
    · exact congrArg _ (Finset.sum_congr rfl fun i _ => map_smul f _ (pZ.G i))
    · exact Finset.sum_congr rfl fun j _ => map_smul f (b j) (pZ.GI j)
  -- both inclusions are `hf` read in the two directions; the exponents never move
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, hf a b⟩
  · rintro y ⟨a, b, ha, hb, hy⟩
    refine ⟨pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, b j • pZ.GI j,
      ⟨a, b, ha, hb, rfl⟩, ?_⟩
    rw [hy]
    exact hf a b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
