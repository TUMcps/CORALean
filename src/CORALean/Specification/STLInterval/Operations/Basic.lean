module

public import CORALean.Specification.STLInterval.Definitions.Fields
public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `Specification/STLInterval/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ====================================  `STLInterval.dim`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@stlInterval/dim.m`: STL intervals are one-dimensional. -/
def STLInterval.dim (_ : STLInterval) : ℕ := 1


-- ==================================  `STLInterval.fieldsOf`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The stored fields of an interval object: none for the empty interval. -/
def STLInterval.fieldsOf : STLInterval → Option STLInterval.Fields
  | .empty => none
  | .nonempty l u lc rc _ _ _ => some ⟨l, some u, lc, rc⟩


-- ================================  `STLInterval.leftClosure`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@stlInterval/leftClosure.m`: the interval with its lower end closed, unless it is empty or
unbounded below. -/
noncomputable def STLInterval.leftClosure : STLInterval → STLInterval
  | .empty => .empty
  | I@(.nonempty l u _ rc _ _ _) => if l = ⊥ then I else stlInterval l u true rc


-- ================================  `STLInterval.rightClosure`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@stlInterval/rightClosure.m`: the interval with its upper end closed, unless it is empty or
unbounded above. -/
noncomputable def STLInterval.rightClosure : STLInterval → STLInterval
  | .empty => .empty
  | I@(.nonempty l u lc _ _ _ _) => if u = ⊤ then I else stlInterval l u lc true


-- ==================================  `STLInterval.toRight`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@stlInterval/toRight.m`: `(upper, ∞)`, or `[upper, ∞)` when the upper end is open. `none` is
CORA's `CORA:emptySet` error on the empty interval. -/
noncomputable def STLInterval.toRight : STLInterval → Option STLInterval
  | .empty => none
  | .nonempty _ u _ rc _ _ _ => some (stlInterval u ⊤ (!rc) false)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
