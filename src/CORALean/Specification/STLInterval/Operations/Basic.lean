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


-- ================================  `STLInterval.emptyBounds`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `isemptyobject` of `stlInterval(lb,ub,lc,rc)` for real bounds, `ub` possibly `inf`. -/
def STLInterval.emptyBounds {T : Type} [LinearOrder T] (lb : T) (ub : WithTop T) (lc rc : Bool) :
    Bool := if ub < lb ∨ (ub = lb ∧ ¬ (lc = true ∧ rc = true)) then true else false


-- ==================================  `STLInterval.fieldsOf`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The stored fields of an interval object: none for the empty interval. -/
def STLInterval.fieldsOf : STLInterval → Option STLInterval.Fields
  | .empty => none
  | .nonempty l u lc rc _ _ _ _ => some ⟨l, some u, lc, rc⟩


-- ================================  `STLInterval.leftClosure`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@stlInterval/leftClosure.m`: the interval with its lower end closed, unless it is empty or
unbounded below. -/
noncomputable def STLInterval.leftClosure : STLInterval → STLInterval
  | .empty => .empty
  | I@(.nonempty l u _ rc _ _ _ z) => if l = ⊥ then I else stlInterval l u true rc z


-- =================================  `STLInterval.lowerBound`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The lower bound as a real; the empty interval gets `0`. -/
noncomputable def STLInterval.lowerBound : STLInterval → ℝ
  | .empty => 0
  | .nonempty l _ _ _ _ _ _ _ => l.toReal


-- ================================  `STLInterval.lowerClosed`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Whether the lower end is closed; the empty interval gets `false`. -/
def STLInterval.lowerClosed : STLInterval → Bool
  | .empty => false
  | .nonempty _ _ lc _ _ _ _ _ => lc


-- ================================  `STLInterval.rightClosure`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@stlInterval/rightClosure.m`: the interval with its upper end closed, unless it is empty or
unbounded above. -/
noncomputable def STLInterval.rightClosure : STLInterval → STLInterval
  | .empty => .empty
  | I@(.nonempty l u lc _ _ _ _ z) => if u = ⊤ then I else stlInterval l u lc true z


-- ==================================  `STLInterval.toRight`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- `@stlInterval/toRight.m`: `(upper, ∞)`, or `[upper, ∞)` when the upper end is open. `none` is
CORA's `CORA:emptySet` error on the empty interval. -/
noncomputable def STLInterval.toRight : STLInterval → Option STLInterval
  | .empty => none
  | .nonempty l u _ rc _ _ hlt z => some (stlInterval u ⊤ (!rc) false (z.trans (by grind)))


-- =================================  `STLInterval.upperBound`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The upper bound as a real or `inf`; the empty interval gets `0`. -/
noncomputable def STLInterval.upperBound : STLInterval → WithTop ℝ
  | .empty => ((0 : ℝ) : WithTop ℝ)
  | .nonempty _ u _ _ _ _ _ _ => if u = ⊤ then ⊤ else ((u.toReal : ℝ) : WithTop ℝ)


-- ================================  `STLInterval.upperClosed`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Whether the upper end is closed; the empty interval gets `false`. -/
def STLInterval.upperClosed : STLInterval → Bool
  | .empty => false
  | .nonempty _ _ _ rc _ _ _ _ => rc


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
