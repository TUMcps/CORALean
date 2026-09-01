import CORALean.ContSet.ContSet.API

/-!
# Intervals: the representation

CORA's `interval`, with the same `inf` and `sup` fields, denoting the points
each coordinate's bounds admit.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   18-August-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

structure Interval (n : ℕ) where
  inf : Vec ℝ n
  sup : Vec ℝ n

/-- `sup i < inf i` denotes the empty set `∅` -/
def Interval.construct (I : Interval n) : Set (Vec ℝ n) :=
  {x | ∀ i, I.inf i ≤ x i ∧ x i ≤ I.sup i}

/-- checked in `Theorems.isNonempty_iff` -/
def Interval.IsNonempty (I : Interval n) : Prop := ∀ i, I.inf i ≤ I.sup i

end CORALean.Real
