import CORALean.Examples.Bench.RandVerifyInstance
import CORALean.Examples.Bench.RandVerifyJsonNumber

/-!
# `randverify`: reading an instance

Tolerant of the field names: `A`, `B`, `C`; `X0` (`x0`, `R0`); `U` (`u`); `tend` (`tFinal`,
`tfinal`, `T`); `unsafeSet` (`unsafe_set`, `unsafeSets`, `spec`). A box is `{lb, ub}`, `{inf, sup}`
or `{lowerbound, upperbound}` (CORA's export) of vectors, or an array of `{lb, ub}` (scalars) or
`[lo, hi]` per dimension; the unsafe sets are an array of such boxes in output space. A number is a
JSON number or a string `parseRandString` reads.

## Inputs
* `name` – instance name
* `j` – instance JSON

## Output
* parsed instance or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private def aux_aliasA := ["A", "a"]
private def aux_aliasB := ["B", "b"]
private def aux_aliasC := ["C", "c"]
private def aux_aliasX0 := ["X0", "x0", "R0", "r0"]
private def aux_aliasU := ["U", "u"]
private def aux_aliasT := ["tend", "tFinal", "tfinal", "t_final", "T", "tEnd"]
private def aux_aliasUnsafe :=
    ["unsafeSet", "unsafe_set", "unsafeSets", "unsafe_sets", "unsafe", "spec"]
private def aux_loKeys := ["inf", "lb", "lower", "lowerbound", "lowerBound", "min", "lo", "infimum"]
private def aux_hiKeys :=
    ["sup", "ub", "upper", "upperbound", "upperBound", "max", "hi", "supremum"]

/-- The first of `names` that `j` has. -/
private def aux_find (j : Json) (names : List String) : Option Json :=
  names.findSome? fun k => (j.getObjVal? k).toOption

/-- A vector, or a scalar as a one-entry vector. -/
private def aux_vec : Json → Except String (Array ℚ)
  | .arr a => a.mapM parseRandJson
  | j => (fun q => #[q]) <$> parseRandJson j

private def aux_zipBox (lo hi : Array ℚ) : Except String (Array (ℚ × ℚ)) := do
  if lo.size ≠ hi.size then throw "a box's lower and upper bounds differ in length"
  let b := lo.zip hi
  if b.any fun (l, h) => h < l then throw "a box has a lower bound above its upper bound"
  pure b

/-- A box: `{lb, ub}` of vectors, or an array of `{lb, ub}` / `[lo, hi]`, one per dimension. -/
private def aux_box : Json → Except String (Array (ℚ × ℚ))
  | .arr es => es.mapM fun
    | .arr #[l, h] => do
      let lq ← parseRandJson l
      let hq ← parseRandJson h
      if hq < lq then throw "an interval has a lower bound above its upper bound"
      pure (lq, hq)
    | e => do
      match aux_find e aux_loKeys, aux_find e aux_hiKeys with
      | some l, some h => do
        let lq ← parseRandJson l
        let hq ← parseRandJson h
        if hq < lq then throw "an interval has a lower bound above its upper bound"
        pure (lq, hq)
      | _, _ => throw s!"`{e.compress}` is not an interval (`lb`/`ub` or `inf`/`sup`)"
  | j => match aux_find j aux_loKeys, aux_find j aux_hiKeys with
    | some l, some h => do aux_zipBox (← aux_vec l) (← aux_vec h)
    | _, _ => throw s!"`{j.compress}` is not a box (`lb`/`ub` or `inf`/`sup`)"

/-- Whether `j` is one box of several, rather than the dimensions of a single one. -/
private def aux_isSet : Json → Bool
  | .arr es => es.any fun | .arr _ => true | .obj _ => true | _ => false
  | j => match aux_find j aux_loKeys with
    | some (.arr _) => true
    | _ => false

private def aux_matrix (j : Json) : Except String (Array (Array ℚ)) := do (← j.getArr?).mapM aux_vec

private def aux_need (j : Json) (what : String) (names : List String) : Except String Json :=
  match aux_find j names with
  | some v => pure v
  | none => throw s!"field `{what}` (or {names}) is missing"

/-- Everything the file carries beyond the system. -/
private def aux_extra (j : Json) : Json :=
  let known := aux_aliasA ++ aux_aliasB ++ aux_aliasC ++ aux_aliasX0 ++ aux_aliasU ++
    aux_aliasT ++ aux_aliasUnsafe
  match j with
  | .obj kvs => Json.mkObj (kvs.toList.filter fun (k, _) => !known.contains k)
  | _ => Json.null


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The instance `j` states, named `name`. -/
def parseRandInstance (name : String) (j : Json) : Except String RandInstance := do
  let A ← aux_matrix (← aux_need j "A" aux_aliasA)
  let B ← aux_matrix (← aux_need j "B" aux_aliasB)
  let C ← aux_matrix (← aux_need j "C" aux_aliasC)
  let x0 ← aux_box (← aux_need j "X0" aux_aliasX0)
  let u ← aux_box (← aux_need j "U" aux_aliasU)
  let tend ← parseRandJson (← aux_need j "tend" aux_aliasT)
  let us ← aux_need j "unsafeSet" aux_aliasUnsafe
  let unsafeSets ← match us with
    | .arr es => if es.size > 0 && es.all aux_isSet then es.mapM aux_box else (#[·]) <$> aux_box us
    | _ => (#[·]) <$> aux_box us
  pure { name, A, B, C, x0, u, tend, unsafeSets, extra := aux_extra j }

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
