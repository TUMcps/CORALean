import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# A zonotope contains its centre

The zero coefficient vector, and nothing more. Small, and worth a name: it is
what says a zonotope is *nonempty*, which is the hypothesis Rådström's
cancellation asks of the set it cancels — so every inner approximation built by
subtracting a zonotope off an enclosure goes through here.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.centre_mem_construct (Z : Zonotope α) : Z.c ∈ Z.construct :=
  ⟨fun _ => 0, fun _ => by simp, by simp⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
