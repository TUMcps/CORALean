import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes

/-!
# `ConPolyZono.map` is exactly the image under a linear map

The same factors and independent coefficients work in both directions, and the
constraint is the same proposition about them before and after — a linear map of
the ambient space moves points, not factors. Linearity carried through the two
sums is then the whole proof.

`mtimes_exact` is this at `A *ᵥ ·`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

theorem ConPolyZono.map_exact (f : α →ₗ[ℝ] β) (C : ConPolyZono α) :
    f '' C.construct = (C.map f).construct := by
  have hf : ∀ (a : Fin C.p → ℝ) (b : Fin C.q → ℝ),
      f (C.c + ∑ i, PolyZonotope.monomial C.E a i • C.G i + ∑ j, b j • C.GI j)
        = (C.map f).c + ∑ i, PolyZonotope.monomial (C.map f).E a i • (C.map f).G i
            + ∑ j, b j • (C.map f).GI j := by
    intro a b
    rw [map_add, map_add, map_sum, map_sum]
    congr 1
    · exact congrArg _ (Finset.sum_congr rfl fun i _ => map_smul f _ (C.G i))
    · exact Finset.sum_congr rfl fun j _ => map_smul f (b j) (C.GI j)
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨a, b, ha, hb, hsat, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, (ConPolyZono.satisfies_map f C a).mpr hsat, hf a b⟩
  · rintro y ⟨a, b, ha, hb, hsat, hy⟩
    refine ⟨C.c + ∑ i, PolyZonotope.monomial C.E a i • C.G i + ∑ j, b j • C.GI j,
      ⟨a, b, ha, hb, (ConPolyZono.satisfies_map f C a).mp hsat, rfl⟩, ?_⟩
    rw [hy]
    exact hf a b

theorem ConPolyZono.mtimes_exact {k n : ℕ} (M : Mat ℝ k n) (C : ConPolyZono (Vec ℝ n)) :
    (M *ᵥ ·) '' C.construct = (ConPolyZono.mtimes M C).construct :=
  ConPolyZono.map_exact (Matrix.mulVecLin M) C

end CORALean.Real
