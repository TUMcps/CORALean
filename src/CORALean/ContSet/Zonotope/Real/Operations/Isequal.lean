module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.isequal`

CORA's `@zonotope/isequal.m` for two zonotopes: the centres agree to the tolerance, and the
generator matrices, each `compact_(.,'all')`ed, are equal up to the order of the columns
(`compareMatrices`). Here the tolerance is `0` and the generators are compared as they are,
column by column, which is stricter than CORA on both counts: neither the reordering of columns
nor the merging of parallel generators is modelled. So the test is sound, not exact (the
converse fails: the generator lists 1, 1 and 2 generate the same interval).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/isequal` at tolerance `0`, without compaction: the same number of generators, the
same centre, and the same generators in the same order. -/
def Zonotope.isequal (Z S : Zonotope α) : Prop :=
  ∃ e : Z.h = S.h, Z.c = S.c ∧ ∀ j, Z.G j = S.G (Fin.cast e j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
