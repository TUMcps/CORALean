import CORALean.Examples.Oracle.Ops.IntervalOps
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Specification.Instances
import CORALean.Specification.Operations.Check

/-!
# The specification op: CORA's `specification/check`

`specification.check` is `Specification.check`: a specification is a `set` and a `kind`
(`safeSet`, `unsafeSet`, `invariant`), checked against the computed set `S`. The set of the
specification is a box `{"inf","sup"}` or a halfspace polytope `{"A","b",...}` (the forms
`Specification.Instances` has `Contains` and `IsDisjoint` for), the checked set a box `I` or a
zonotope `Z`. `value` is `true` where `Contains` (safe set, invariant) or `IsDisjoint` (unsafe set)
proves the requirement; `false` says only that it was not shown.

## Inputs
* `req` – request

## Output
* the kind, or the response fields
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       03-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The kind of a specification, by CORA's names. -/
def specKindField (req : Json) : Except String Specification.Kind := do
  match ← strField req "kind" with
  | "safeSet" => pure .safeSet
  | "unsafeSet" => pure .unsafeSet
  | "invariant" => pure .invariant
  | k => throw s!"check: `kind` must be safeSet, unsafeSet or invariant, not `{k}`"

/-- `specification.check`: `Specification.check` of the specification (`set`, `kind`) against the
box `I` or the zonotope `Z`. -/
def handleSpecificationCheck (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "check" req ["set", "kind", "I", "Z"]
  let kind ← specKindField req
  let sj ← field req "set"
  -- the checked set, a box or a zonotope of dimension `n`
  let probe (n : Nat) : Except String (Interval (Vec 𝕋 n) ⊕ Zonotope (Vec 𝕋 n)) :=
    match fieldOpt req "I", fieldOpt req "Z" with
    | some ij, none => .inl <$> parseIntervalVecFixed dops.readExact n ij
    | none, some zj => .inr <$> parseZonotopeFixed dops.readExact n zj
    | _, _ => throw "check: needs exactly one of `I` (a box) and `Z` (a zonotope)"
  -- the specification's set is a halfspace polytope where it has `A`, else a box
  if (fieldOpt sj "A").isSome then
    let d ← parseHPolytope dops.readExact sj
    match ← probe d.n with
    | .inl I => valueBool (Specification.check (⟨d.P, kind⟩ : Specification _) I)
    | .inr Z => valueBool (Specification.check (⟨d.P, kind⟩ : Specification _) Z)
  else
    -- the box instances are generic over a family, fixed to `ℐ𝒱` here as in `interval.contains`
    let b ← parseBox dops.readExact sj
    match ← probe b.n with
    | .inl I =>
      letI : Contains (Interval (Vec 𝕋 b.n)) (Interval (Vec 𝕋 b.n)) :=
        containsBoxOuter (S := ℐ𝒱[𝕋])
      letI : IsDisjoint (Interval (Vec 𝕋 b.n)) (Interval (Vec 𝕋 b.n)) :=
        isDisjointBoxOuter (S := ℐ𝒱[𝕋])
      valueBool (Specification.check (⟨b.I, kind⟩ : Specification _) I)
    | .inr Z => valueBool (Specification.check (⟨b.I, kind⟩ : Specification _) Z)

/-- Every op of this file, without the `specification.` prefix. -/
def specificationOpNames : List String := [ "check" ]

/-- `op` of `specification.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleSpecificationOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "check" => some (handleSpecificationCheck dops req)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
