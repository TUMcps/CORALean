module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Fullspace.Real.Fullspace
public import Mathlib.Data.ENNReal.Basic

@[expose] public section

/-!
# `ContSet/Fullspace/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n m : ℕ}


-- ===================================  `Fullspace.convHull`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fullspace/convHull_`: the full space.

CORA's `@fullspace/convHull_`: the hull of the full space and anything is the full space. -/
def Fullspace.convHull (F : Fullspace n) {S : Type} (_ : S) : Fullspace n := F


-- =====================================  `Fullspace.Inf`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fullspace.Inf(n)`.

CORA's `fullspace.Inf(n)`: the full space in `n` dimensions, the only value of the type. -/
def Fullspace.Inf (n : ℕ) : Fullspace n := ⟨⟩


-- ==================================  `Fullspace.isBounded`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `isBounded` of the fullspace, as the `Bool` it answers: `dim(fs) == 0`: `false` in every
positive dimension. Holds no scalar and computes nothing numeric; `Fullspace.isBounded_iff` says
it is boundedness of the set. -/
def Fullspace.isBounded (_ : Fullspace n) : Bool := decide (n = 0)


-- ====================================  `Fullspace.radius`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fullspace/radius`: `Inf`.

CORA's `@fullspace/radius`: `Inf`. At dimension `0` CORA answers `NaN`; that case is not claimed. -/
def Fullspace.radius (_ : Fullspace n) : ENNReal := ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
