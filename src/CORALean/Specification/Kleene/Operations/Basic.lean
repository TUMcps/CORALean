module

public import CORALean.Specification.Kleene.Kleene

@[expose] public section

/-!
# `Kleene/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").

`floor`, `ceil`, `join` and `IsRefinedBy` are `⌊·⌋`, `⌈·⌉`, `⊔₁` and `≺` of
[1, Sec. 4.2 (refinements)]: a Boolean value refines a Kleene one.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ======================================  `Kleene.ceil`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `⌈k⌉`, [1, Sec. 4.2 (refinements)]: `Unknown` replaced by `true`. -/
def Kleene.ceil : Kleene → Bool
  | .ff => false
  | _ => true


-- ======================================  `Kleene.floor`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `⌊k⌋`, [1, Sec. 4.2 (refinements)]: `Unknown` replaced by `false`. -/
def Kleene.floor : Kleene → Bool
  | .tt => true
  | _ => false


-- ====================================  `Kleene.fromBool`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `kleene.fromBool(b)`: `True` for `b`, `False` otherwise. -/
def Kleene.fromBool (b : Bool) : Kleene := if b then .tt else .ff


-- ===================================  `Kleene.IsRefinedBy`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `b ≺ k`, [1, Sec. 4.2 (refinements)]: `k` is refined by the Boolean value `b` if `k` is not
`Unknown` only when `b` is `k`. -/
def Kleene.IsRefinedBy (k : Kleene) (b : Bool) : Prop := k ≠ .uu → Kleene.fromBool b = k


-- ====================================  `Kleene.isUnknown`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `unk` of `kleeneToBoolUnk(k)`: whether `k` is `Unknown`. -/
def Kleene.isUnknown : Kleene → Bool
  | .uu => true
  | _ => false


-- ======================================  `Kleene.join`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `v ⊔₁ v'`, [1, Sec. 4.2 (refinements)]: `v` if `v = v'`, else `Unknown`. -/
def Kleene.join (v v' : Bool) : Kleene := if v = v' then Kleene.fromBool v else .uu


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
