module

public import CORALean.Global.IsEqvTop
public import CORALean.Specification.STLInterval.Definitions.Fields
public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `Specification/STLInterval/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").

The intervals are over the scalar `𝕋` a layer computes in; nothing here rounds.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ==================================  `STLInterval.addUpTop`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The sum of two upper bounds, rounded up; `inf` if either is. -/
def STLInterval.addUpTop (u₁ u₂ : WithTop 𝕋) : WithTop 𝕋 :=
  match u₁, u₂ with
  | some x, some y => some (addUp x y)
  | _, _ => ⊤


-- ====================================  `STLInterval.dim`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@stlInterval/dim.m`: STL intervals are one-dimensional. -/
def STLInterval.dim (_ : STLInterval 𝕋) : ℕ := 1


-- ================================  `STLInterval.emptyBounds`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `isemptyobject` of `stlInterval(lb,ub,lc,rc)` for real bounds, `ub` possibly `inf`. -/
def STLInterval.emptyBounds {T : Type} [TimeOrder T] (lb : T) (ub : WithTop T) (lc rc : Bool) :
    Bool := if ub < lb ∨ (TimeOrder.IsEqvTop ub lb ∧ ¬ (lc = true ∧ rc = true)) then true else false


-- ==================================  `STLInterval.fieldsOf`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The stored fields of an interval object: none for the empty interval. -/
def STLInterval.fieldsOf : STLInterval 𝕋 → Option (STLInterval.Fields 𝕋)
  | .empty => none
  | .nonempty l u lc rc _ _ _ => some ⟨l, some u, lc, rc⟩


-- ================================  `STLInterval.leftClosure`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@stlInterval/leftClosure.m`: the interval with its lower end closed, unless it is empty; the
lower bound is never `-inf`. -/
def STLInterval.leftClosure [ExactLe 𝕋] : STLInterval 𝕋 → STLInterval 𝕋
  | .empty => .empty
  | .nonempty l u _ rc _ _ z => stlInterval l u true rc z


-- =================================  `STLInterval.lowerBound`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The lower bound; the empty interval gets `0`. -/
def STLInterval.lowerBound : STLInterval 𝕋 → 𝕋
  | .empty => zero
  | .nonempty l _ _ _ _ _ _ => l


-- ================================  `STLInterval.lowerClosed`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Whether the lower end is closed; the empty interval gets `false`. -/
def STLInterval.lowerClosed : STLInterval 𝕋 → Bool
  | .empty => false
  | .nonempty _ _ lc _ _ _ _ => lc


-- ================================  `STLInterval.rightClosure`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@stlInterval/rightClosure.m`: the upper end closed, unless empty or unbounded above. -/
def STLInterval.rightClosure [ExactLe 𝕋] : STLInterval 𝕋 → STLInterval 𝕋
  | .empty => .empty
  | I@(.nonempty _ none _ _ _ _ _) => I
  | .nonempty l u@(some _) lc _ _ _ z => stlInterval l u lc true z


-- ==================================  `STLInterval.subUpTop`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The difference of two upper bounds, rounded up; `inf` unless both are stored. -/
def STLInterval.subUpTop (u₁ u₂ : WithTop 𝕋) : WithTop 𝕋 :=
  match u₁, u₂ with
  | some x, some y => some (subUp x y)
  | _, _ => ⊤


-- =================================  `STLInterval.upperBound`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The upper bound, or `inf`; the empty interval gets `0`. -/
def STLInterval.upperBound : STLInterval 𝕋 → WithTop 𝕋
  | .empty => ((zero : 𝕋) : WithTop 𝕋)
  | .nonempty _ u _ _ _ _ _ => u


-- ================================  `STLInterval.upperClosed`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Whether the upper end is closed; the empty interval gets `false`. -/
def STLInterval.upperClosed : STLInterval 𝕋 → Bool
  | .empty => false
  | .nonempty _ _ _ rc _ _ _ => rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
