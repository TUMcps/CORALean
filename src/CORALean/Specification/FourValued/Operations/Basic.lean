module

public import CORALean.Specification.FourValued.FourValued
public import CORALean.Specification.Kleene.Kleene

@[expose] public section

/-!
# `FourValued/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").

`floor`, `ceil`, `join` and `IsRefinedBy` are `⌊·⌋`, `⌈·⌉`, `⊔₂` and `≺` of
[1, Sec. 4.3 (refinements)]: a Kleene value refines a four-valued one.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ====================================  `FourValued.ceil`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `⌈v⌉`, [1, Sec. 4.3 (refinements)]: `Inconclusive` replaced by `True`. -/
def FourValued.ceil : FourValued → Kleene
  | .ff => .ff
  | .uu => .uu
  | _ => .tt


-- ====================================  `FourValued.floor`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `⌊v⌋`, [1, Sec. 4.3 (refinements)]: `Inconclusive` replaced by `False`. -/
def FourValued.floor : FourValued → Kleene
  | .tt => .tt
  | .uu => .uu
  | _ => .ff


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


-- =================================  `FourValued.IsRefinedBy`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `k ≺ v`, [1, Sec. 4.3 (refinements)]: `v` is refined by the Kleene value `k` if `v` is not
`Inconclusive` only when `k` is `v`. -/
def FourValued.IsRefinedBy (v : FourValued) (k : Kleene) : Prop :=
  v ≠ .ii → FourValued.fromKleene k = v


-- ====================================  `FourValued.join`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `v ⊔₂ v'`, [1, Sec. 4.3 (refinements)]: `v` if `v = v'`, else `Inconclusive`. -/
def FourValued.join (v v' : Kleene) : FourValued := if v = v' then FourValued.fromKleene v else .ii


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
