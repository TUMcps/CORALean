module

public import CORALean.ContSet.ConZonotope.Real.Operations.Map

@[expose] public section

/-!
# `ConZonotope.map` is exactly the image under a linear map

The same coefficients work in both directions [1, Prop. 1] and satisfy the same constraints,
which the map never sees. So a constrained zonotope propagates through a linear
system as exactly as a zonotope does.

## Inputs
* `f` – linear map
* `cZ` – constrained zonotope

## Hypotheses
* none

## Conclusion
* the result is exactly the image under the map

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.map_exact (f : α →ₗ[ℝ] β) (cZ : ConZonotope α) : -- --- CONCL ---
    ⇑f '' cZ.construct = (cZ.map f).construct := by -- --- PROOF ---
  have hf : ∀ b : Fin cZ.h → ℝ, f (cZ.c + ∑ j, b j • cZ.G j)
      = (cZ.map f).c + ∑ j, b j • (cZ.map f).G j := by
    intro b
    rw [map_add, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => map_smul f (b j) (cZ.G j))
  -- both inclusions are `hf` read in the two directions; the polytope never moves
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨b, hb, hA, rfl⟩, rfl⟩
    exact ⟨b, hb, hA, hf b⟩
  · rintro y ⟨b, hb, hA, hy⟩
    refine ⟨cZ.c + ∑ j, b j • cZ.G j, ⟨b, hb, hA, rfl⟩, ?_⟩
    rw [hy]
    exact hf b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
