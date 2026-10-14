module

public import CORALean.Specification.Kleene.Kleene

@[expose] public section

/-!
# `Kleene/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ====================================  `Kleene.fromBool`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `kleene.fromBool(b)`: `True` for `b`, `False` otherwise. -/
def Kleene.fromBool (b : Bool) : Kleene := if b then .tt else .ff


-- ====================================  `Kleene.isUnknown`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `unk` of `kleeneToBoolUnk(k)`: whether `k` is `Unknown`. -/
def Kleene.isUnknown : Kleene → Bool
  | .uu => true
  | _ => false


-- =======================================  `Kleene.not`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `~phi`: swaps `True` and `False`, keeps `Unknown`. -/
def Kleene.not : Kleene → Kleene
  | .tt => .ff
  | .ff => .tt
  | .uu => .uu


-- ====================================  `Kleene.ofBoolUnk`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `boolUnkToKleene(bool,unk)`: `Unknown` if `unk`, else `fromBool(bool)`. -/
def Kleene.ofBoolUnk (b unk : Bool) : Kleene := if unk then .uu else Kleene.fromBool b


-- =====================================  `Kleene.toBool`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `boolVal` of `kleeneToBoolUnk(k)`: `true` for `True`, else `false` (`Unknown` too). -/
def Kleene.toBool : Kleene → Bool
  | .tt => true
  | _ => false


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
