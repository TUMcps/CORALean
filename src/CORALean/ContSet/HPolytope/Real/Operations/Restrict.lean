module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# `HPolytope.restrict`

The rows of a polytope picked by two index sets, in their order: CORA's `A(idx,:)`, `b(idx)`,
`Ae(idx,:)`, `be(idx)`, which every step of `compact_` ends with. The others are deleted;
`Theorems.RestrictConstruct` says what is left.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inequality rows indexed by `S` and the equality rows indexed by `T`. -/
noncomputable def HPolytope.restrict (P : HPolytope α) (S : Finset (Fin P.m))
    (T : Finset (Fin P.me)) : HPolytope α where
  m := S.card
  A := fun k => P.A (S.equivFin.symm k).1
  b := fun k => P.b (S.equivFin.symm k).1
  me := T.card
  Ae := fun k => P.Ae (T.equivFin.symm k).1
  be := fun k => P.be (T.equivFin.symm k).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
