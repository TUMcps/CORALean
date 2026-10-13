import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.isequal`

CORA's `@conPolyZono/isequal.m` for two constrained polynomial zonotopes: both are
`compact_(.,'all')`ed, the identifier vectors are aligned (`mergeExpMatrix`), `[G; E]` agree up to
the order of the columns, `EC` and `[b A]` agree row by row up to sign, and the independent parts
are compared as zonotopes. Here the tolerance is `0` and the data are compared as they are, in
order, with no compaction, alignment or row sign flips, so the test is sound, not exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conPolyZono/isequal` at tolerance `0`, without compaction or reordering. -/
def ConPolyZono.isequal (Z S : ConPolyZono α) : Prop :=
  ∃ (ep : Z.p = S.p) (eh : Z.h = S.h) (eq : Z.q = S.q) (_ : Z.m = S.m) (es : Z.s = S.s),
    Z.c = S.c
    ∧ (∀ j, Z.G j = S.G (Fin.cast eh j))
    ∧ (∀ k i, Z.E k i = S.E (Fin.cast ep k) (Fin.cast eh i))
    ∧ (∀ j, Z.GI j = S.GI (Fin.cast eq j))
    ∧ HEq Z.A S.A ∧ HEq Z.b S.b
    ∧ ∀ k i, Z.EC k i = S.EC (Fin.cast ep k) (Fin.cast es i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
