import CORALean.ContSet.SpectraShadow.Real.Operations.Map

/-!
# `SpectraShadow.map` is exactly the image under a linear map

The same variables work in both directions: the inequality never sees the
projection, and a linear map carries the sum `c + Σ βᵢ Gᵢ` through term by term.
That a linear image of a spectrahedral shadow is another is what makes the
representation closed under `mtimes`, and every image guarantee here is this one
at a particular map.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.map_exact (f : α →ₗ[ℝ] β) (S : SpectraShadow α) :
    f '' S.construct = (S.map f).construct := by -- --- PROOF ---
  have hf : ∀ b : Fin S.m → ℝ, f (S.c + ∑ j, b j • S.G j)
      = (S.map f).c + ∑ j, b j • (S.map f).G j := by
    intro b
    rw [map_add, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => map_smul f (b j) (S.G j))
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, hf b⟩
  · rintro y ⟨b, hb, hy⟩
    refine ⟨S.c + ∑ j, b j • S.G j, ⟨b, hb, rfl⟩, ?_⟩
    rw [hy]
    exact hf b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
