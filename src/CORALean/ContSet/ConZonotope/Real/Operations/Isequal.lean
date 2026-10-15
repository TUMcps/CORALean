module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope

@[expose] public section

/-!
# `ConZonotope.isequal`

CORA's `@conZonotope/isequal.m` for two constrained zonotopes: after the emptiness and point
special cases, the centers agree to the tolerance and `[G; A]` and `[A b]` agree up to the order
of the columns (`compareMatrices`), else the vertices are compared. Here the tolerance is `0` and
the data are compared as they are, which is stricter than CORA: the generators and the constraint
polytope must be equal field by field, in order, and neither the vertex comparison nor the
point and emptiness cases are modelled. So the test is sound, not exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conZonotope/isequal` at tolerance `0`, without compaction: the same number of generators,
the same center, the same generators in the same order, and the same constraint polytope. -/
def ConZonotope.isequal [AddCommGroup α] [Module ℝ α] (Z S : ConZonotope α) : Prop :=
  ∃ e : Z.h = S.h, Z.c = S.c ∧ (∀ j, Z.G j = S.G (Fin.cast e j)) ∧ HEq Z.P S.P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
