import CORALean.ContSet.LevelSet.Real.LevelSet
import Mathlib.Data.Finset.Sort

/-!
# `LevelSet.restrict`

The constraints of a level set at a chosen set of indices, in order, each with its own operator:
what CORA's `splitEquality` builds with `ls.eq(ind)` and `ls.compOp(ind)`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The constraints of `L` at the indices `s`, in order, each with its own operator. -/
def LevelSet.restrict {n : ℕ} (L : LevelSet n) (s : Finset (Fin L.m)) : LevelSet n where
  m := s.card
  f x := fun j => L.f x (s.orderEmbOfFin rfl j)
  op := fun j => L.op (s.orderEmbOfFin rfl j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
