import CORALean.ContSet.HPolytope.Real.Operations.Comap

/-!
# `HPolytope.comap` is exactly the preimage

By `rfl`: precomposing every constraint with `f` is what asking the constraints
about `f x` means.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.comap_exact (f : β →ₗ[ℝ] α) (P : HPolytope α) :
    (HPolytope.comap f P).construct = f ⁻¹' P.construct := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
