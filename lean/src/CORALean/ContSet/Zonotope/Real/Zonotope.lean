import CORALean.ContSet.Interval.Real.API

/-!
# Zonotopes: the representation

CORA's `zonotope`, with the same centre `c` and generator matrix `G`, denoting
every point the generators reach from `c` with coefficients in `[-1, 1]`.

The generator count is a field, not a type index: operations grow it freely and
`reduce` is what bounds it, where the algorithm asks rather than everywhere.

Separate from `Operations`, which every operation file builds on.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   18-August-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

structure Zonotope (n : ℕ) where
  h : ℕ
  c : Vec ℝ n
  G : Mat ℝ n h

def Zonotope.construct (Z : Zonotope n) : Set (Vec ℝ n) :=
  {x | ∃ β : Vec ℝ Z.h, (∀ j, |β j| ≤ 1) ∧ ∀ i, x i = Z.c i + ∑ j, Z.G i j * β j}

end CORALean.Real
