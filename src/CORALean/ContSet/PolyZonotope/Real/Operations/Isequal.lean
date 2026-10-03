import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.isequal`

CORA's `@polyZonotope/isequal.m` for two polynomial zonotopes: both are `compact_(.,'all')`ed,
the identifier vectors are aligned (`mergeExpMatrix`), and `[G; E]`, `GI` and `c` agree to the
tolerance up to the order of the columns (`compareMatrices`). Here the tolerance is `0` and the
data are compared as they are: the same factor, generator and independent-generator counts, and
the same centre, generators, exponent matrix and independent generators, in order. That is
stricter than CORA, which neither reorders columns, compacts nor aligns identifiers here, so the
test is sound, not exact.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polyZonotope/isequal` at tolerance `0`, without compaction or reordering. -/
def PolyZonotope.isequal (Z S : PolyZonotope α) : Prop :=
  ∃ (ep : Z.p = S.p) (eh : Z.h = S.h) (eq : Z.q = S.q), Z.c = S.c
    ∧ (∀ j, Z.G j = S.G (Fin.cast eh j))
    ∧ (∀ k i, Z.E k i = S.E (Fin.cast ep k) (Fin.cast eh i))
    ∧ ∀ j, Z.GI j = S.GI (Fin.cast eq j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
