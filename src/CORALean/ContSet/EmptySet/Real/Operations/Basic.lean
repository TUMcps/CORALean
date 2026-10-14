module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.EmptySet.Real.EmptySet
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.VPolytope.Real.Operations.EmptySet
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `ContSet/EmptySet/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n m : ℕ}


-- ===================================  `EmptySet.convHull`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `emptySet/convHull_`: the other operand.

CORA's `@emptySet/convHull_`: the hull of the empty set and `S` is `S`, returned as it is. -/
def EmptySet.convHull (_ : EmptySet n) {S : Type} (s : S) : S := s


-- =====================================  `EmptySet.empty`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `emptySet.empty(n)`.

CORA's `emptySet.empty(n)`: the empty set in `n` dimensions, the only value of the type. -/
def EmptySet.empty (n : ℕ) : EmptySet n := ⟨⟩


-- ===================================  `EmptySet.interval`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `emptySet/interval`: `Interval.empty n`.

CORA's `@emptySet/interval`: `interval.empty(n)`, the crossed box `Interval.empty`. -/
def EmptySet.interval (_ : EmptySet n) : Interval (Vec ℝ n) := Interval.empty n


-- ====================================  `EmptySet.radius`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `emptySet/radius`: `0`.

CORA's `@emptySet/radius`: `0`. -/
def EmptySet.radius (_ : EmptySet n) : ENNReal := 0


-- ====================================  `EmptySet.volume`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `emptySet/volume_`: `0`.

CORA's `@emptySet/volume_`: `0`. -/
def EmptySet.volume (_ : EmptySet n) : ENNReal := 0


-- ===================================  `EmptySet.vPolytope`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `emptySet/polytope` at vertices: `VPolytope.emptySet`.

CORA's `@emptySet/polytope`, as the vertex representation: no vertices. -/
def EmptySet.vPolytope (_ : EmptySet n) : VPolytope (Vec ℝ n) := VPolytope.emptySet _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
