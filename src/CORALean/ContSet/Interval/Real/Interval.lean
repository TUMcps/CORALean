module

public import CORALean.Global.Entrywise

@[expose] public section

/-!
# Intervals: the representation

CORA's `interval`, with the same `inf` and `sup` fields, denoting the points
each coordinate's bounds admit.

Over any ambient type that has coordinates, so `Interval (Mat ℝ m n)` is CORA's
`intervalMatrix` and needs no separate representation: only which index set the
bounds run over changes.
The interval `[x̲, x̅]` is the one [1, Sec. 2] introduces for CORA's `interval`, also written
`mid ⊕ rad ⊗ [-1, 1]`.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". ARCH16. 3rd
      International Workshop on Applied Verification for Continuous and Hybrid Systems, 2017.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

-- Import guards (CONTRIBUTING, "Import guards and layering"): what must stay out of the closure.

-- Measure theory, whose import closure is larger than this whole layer.
assert_not_exists MeasureTheory.Measure
-- Probability, which sits on top of measure theory.
assert_not_exists ProbabilityTheory.IndepFun
-- Determinants and the spectral theory built on them.
assert_not_exists Matrix.det
-- The analytic special functions; exact enclosures of them belong higher up.
assert_not_exists Real.exp
-- Calculus, which only the dynamics layers need.
assert_not_exists HasDerivAt
-- Inner-product geometry; the sup norm is what this layer uses.
assert_not_exists InnerProductSpace
-- The abstract set class sits above this file.
assert_not_imported CORALean.ContSet.ContSet.Interfaces
-- A concrete representation sits above this file.
assert_not_imported CORALean.ContSet.Zonotope.Real.Zonotope

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- ========================================  MAIN TYPE  ========================================= --

/-- A box between the lower bound `inf` and the upper bound `sup`. -/
structure Interval (α : Type) where
  inf : α
  sup : α

/-- `sup i < inf i` denotes the empty set `∅` -/
def Interval.construct (I : Interval α) : Set α :=
  {x | ∀ i, entry I.inf i ≤ entry x i ∧ entry x i ≤ entry I.sup i}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
