module

public import CORALean.Specification.FourValued.FourValued
public import CORALean.Specification.Kleene.Kleene

@[expose] public section

/-!
# `FourValued/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ==================================  `FourValued.fromBool`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fourValued.fromBool(b)`: `True` for `b`, `False` otherwise. -/
def FourValued.fromBool (b : Bool) : FourValued := if b then .tt else .ff


-- =================================  `FourValued.fromKleene`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fourValued.fromKleene(k)`: `True` and `False` stay, `Unknown` stays `Unknown`. -/
def FourValued.fromKleene : Kleene → FourValued
  | .tt => .tt
  | .ff => .ff
  | .uu => .uu


-- ===============================  `FourValued.isInconclusive`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `inc` of `u2ToKleeneInc(u)`: whether `u` is `Inconclusive`. -/
def FourValued.isInconclusive : FourValued → Bool
  | .ii => true
  | _ => false


-- =================================  `FourValued.ofKleeneInc`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `kleeneIncToU2(k,inc)`: `Inconclusive` if `inc`, else `fromKleene(k)`. -/
def FourValued.ofKleeneInc (k : Kleene) (inc : Bool) : FourValued :=
  if inc then .ii else FourValued.fromKleene k


-- ==================================  `FourValued.toKleene`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `kleeneVal` of `u2ToKleeneInc(u)`: the Kleene value, `Unknown` for `Inconclusive`. -/
def FourValued.toKleene : FourValued → Kleene
  | .tt => .tt
  | .ff => .ff
  | _ => .uu


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
