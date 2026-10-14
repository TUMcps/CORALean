module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.EmptySet.Real.EmptySet
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.VPolytope.Real.Operations.EmptySet
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# `ContSet/EmptySet/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ===================================  `EmptySet.convHull`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `emptySet/convHull_`: the other operand.

CORA's `@emptySet/convHull_`: the hull of the empty set and `S` is `S`, returned as it is. -/
def EmptySet.convHull (_ : EmptySet n) {S : Type} (s : S) : S := s

end CORALean.Real


-- =====================================  `EmptySet.empty`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- `emptySet.empty(n)`.

CORA's `emptySet.empty(n)`: the empty set in `n` dimensions, the only value of the type. -/
def EmptySet.empty (n : ℕ) : EmptySet n := ⟨⟩

end CORALean.Real


-- ===================================  `EmptySet.interval`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `emptySet/interval`: `Interval.empty n`.

CORA's `@emptySet/interval`: `interval.empty(n)`, the crossed box `Interval.empty`. -/
def EmptySet.interval (_ : EmptySet n) : Interval (Vec ℝ n) := Interval.empty n

end CORALean.Real


-- ====================================  `EmptySet.radius`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- `emptySet/radius`: `0`.

CORA's `@emptySet/radius`: `0`. -/
def EmptySet.radius (_ : EmptySet n) : ENNReal := 0

end CORALean.Real


-- ====================================  `EmptySet.volume`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- `emptySet/volume_`: `0`.

CORA's `@emptySet/volume_`: `0`. -/
def EmptySet.volume (_ : EmptySet n) : ENNReal := 0

end CORALean.Real


-- ===================================  `EmptySet.vPolytope`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- `emptySet/polytope` at vertices: `VPolytope.emptySet`.

CORA's `@emptySet/polytope`, as the vertex representation: no vertices. -/
def EmptySet.vPolytope (_ : EmptySet n) : VPolytope (Vec ℝ n) := VPolytope.emptySet _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
