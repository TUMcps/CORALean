import CORALean.ContSet.ConZonotope.Real.Operations.Map

/-!
# `ConZonotope.map` is exactly the image under a linear map

The same coefficients work in both directions and satisfy the same constraints,
which the map never sees. So a constrained zonotope propagates through a linear
system as exactly as a zonotope does.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.map_exact (f : α →ₗ[ℝ] β) (C : ConZonotope α) :
    ⇑f '' C.construct = (C.map f).construct := by
  have hf : ∀ b : Fin C.h → ℝ, f (C.c + ∑ j, b j • C.G j)
      = (C.map f).c + ∑ j, b j • (C.map f).G j := by
    intro b
    rw [map_add, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => map_smul f (b j) (C.G j))
  -- both inclusions are `hf` read in the two directions; the polytope never moves
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨b, hb, hA, rfl⟩, rfl⟩
    exact ⟨b, hb, hA, hf b⟩
  · rintro y ⟨b, hb, hA, hy⟩
    refine ⟨C.c + ∑ j, b j • C.G j, ⟨b, hb, hA, rfl⟩, ?_⟩
    rw [hy]
    exact hf b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
