import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# The full space: the representation

CORA's `fullspace`, the counterpart of `emptySet` and the other set class that
carries no data: everything in `n` dimensions. `HPolytope.fullspace` says the
same thing with no rows, which is a polytope's way of saying it and not a
representation of its own.

The dimension is the index rather than a field, exactly as in `EmptySet`, so
that `ContSet (Fullspace n) (Vec ℝ n)` pins the ambient type.

What it is for: the unit an intersection starts from, and the outer
approximation that assumes nothing. It is unbounded at `0 < n`, so `CompactSet`
is missing from its instances rather than proved.

Real layer only: it holds no scalar, so a float layer would be the same type.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- The whole of `n`-dimensional space, carrying nothing else. -/
structure Fullspace (n : ℕ) where

/-- `Set.univ`, whatever it is applied to. -/
def Fullspace.construct (_ : Fullspace n) : Set (Vec ℝ n) := Set.univ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
