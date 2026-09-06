import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.PolyZonotope.Real.Operations.Map

/-!
# `PolyZonotope.map` is exactly the image under a linear map

The same factors and independent coefficients work in both directions — a linear
map introduces no freedom and removes none — so linearity carried through the
two sums is the whole proof. The monomials are untouched because they are
scalars, which is why the exponent matrix never enters.

`MtimesExact` is this at `A *ᵥ ·`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.map_exact (f : α →ₗ[ℝ] β) (PZ : PolyZonotope α) :
    f '' PZ.construct = (PZ.map f).construct := by -- --- PROOF ---
  have hf : ∀ (a : Fin PZ.p → ℝ) (b : Fin PZ.q → ℝ),
      f (PZ.c + ∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i + ∑ j, b j • PZ.GI j)
        = (PZ.map f).c + ∑ i, PolyZonotope.monomial (PZ.map f).E a i • (PZ.map f).G i
            + ∑ j, b j • (PZ.map f).GI j := by
    intro a b
    rw [map_add, map_add, map_sum, map_sum]
    congr 1
    · exact congrArg _ (Finset.sum_congr rfl fun i _ => map_smul f _ (PZ.G i))
    · exact Finset.sum_congr rfl fun j _ => map_smul f (b j) (PZ.GI j)
  -- both inclusions are `hf` read in the two directions; the exponents never move
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, hf a b⟩
  · rintro y ⟨a, b, ha, hb, hy⟩
    refine ⟨PZ.c + ∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i + ∑ j, b j • PZ.GI j,
      ⟨a, b, ha, hb, rfl⟩, ?_⟩
    rw [hy]
    exact hf a b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
