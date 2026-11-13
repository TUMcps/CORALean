import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.Examples.Oracle.Ops.OpCommon

/-!
# The wire format of a polynomial zonotope

`{"c","G","GI","Exp","E"}`: the center, the dependent generators `G` (`n × h`), the independent
generators `GI` (`n × q`, absent means none), the exponent matrix `Exp` (`p × h`, `{"rows","cols",
"data"}` of integers; absent means the identity with `p = h`, as CORA's default) and the error box
`E` (absent means zero).

## Inputs
* `n` – the dimension
* `j` – the JSON object

## Output
* the set, or an error naming the field
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

section codec

variable {𝕋 : Type} [FloatOps 𝕋] (readD : String → ExactScalar → Except String 𝕋)
  (showD : 𝕋 → String)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A polynomial zonotope of the already-known dimension `n`. -/
def parsePolyZonotopeFixed (n : Nat) (j : Json) : Except String (PolyZonotope (Vec 𝕋 n)) := do
  let c ← parseVecFixed readD n (← field j "c")
  -- the dependent and the independent generators, one column each
  let ⟨h, gMat⟩ ← parseMatRowsFixed readD n (← field j "G")
  let ⟨q, giMat⟩ ← match fieldOpt j "GI" with
    | some v => parseMatRowsFixed readD n v
    | none => pure ⟨0, fun _ k => k.elim0⟩
  let eBox ← match fieldOpt j "E" with
    | some v => parseIntervalVecFixed readD n v
    | none => pure ⟨fun _ => FloatOps.zero, fun _ => FloatOps.zero⟩
  -- the exponent matrix: the identity (CORA's default) or the request's
  match fieldOpt j "Exp" with
  | none => pure ⟨h, h, q, c, (fun l i => gMat i l), Real.PolyZonotope.identE h,
      (fun l i => giMat i l), eBox⟩
  | some ej =>
    let p ← natField ej "rows"
    let hE ← natField ej "cols"
    let data ← arrField ej "data"
    if hE ≠ h then throw s!"`Exp` has {hE} columns, expected {h}"
    if data.size ≠ p * h then throw s!"`Exp` has {data.size} entries, expected {p * h}"
    let vals ← data.mapM fun d => match d.getNat? with
      | .ok k => pure k
      | .error _ => throw "`Exp` entries must be nonnegative integers"
    pure ⟨p, h, q, c, (fun l i => gMat i l), (fun k l => vals.getD (k.val * h + l.val) 0),
      (fun l i => giMat i l), eBox⟩

/-- `pZ` as the wire polynomial zonotope, the reverse of `parsePolyZonotopeFixed`. -/
def printPolyZonotope {n : Nat} (pZ : PolyZonotope (Vec 𝕋 n)) : Json :=
  Json.mkObj
    [ ("c", printVec showD pZ.c), ("G", printMat showD fun i l : Fin _ => pZ.G l i),
      ("GI", printMat showD fun i l : Fin _ => pZ.GI l i),
      ("Exp", Json.mkObj [("rows", Lean.toJson pZ.p), ("cols", Lean.toJson pZ.h),
        ("data", Json.arr ((Array.ofFn fun k : Fin pZ.p =>
          Array.ofFn fun l : Fin pZ.h => Lean.toJson (pZ.E k l)).flatten))]),
      ("E", printIntervalVec showD pZ.I_error) ]

/-- The identifiers of the factors of a wire polynomial zonotope: `id`, else `1..p`. -/
def parsePolyZonotopeIds {n : Nat} (pZ : PolyZonotope (Vec 𝕋 n)) (j : Json) :
    Except String (Array Nat) := do
  let ids ← match fieldOpt j "id" with
    | some _ => natArrField j "id"
    | none => pure ((Array.range pZ.p).map (· + 1))
  if ids.size ≠ pZ.p then throw s!"`id` has {ids.size} entries, the exponent matrix {pZ.p} rows"
  pure ids

/-- `pZ` as the wire polynomial zonotope, with the identifiers of its factors. -/
def printPolyZonotopeIds {n : Nat} (pZ : PolyZonotope (Vec 𝕋 n)) (ids : Array Nat) : Json :=
  (printPolyZonotope showD pZ).setObjVal! "id" (Json.arr (ids.map Lean.toJson))

/-- The identifiers some kept dependent generator still reads. -/
def usedPolyZonotopeIds {n : Nat} (pZ : PolyZonotope (Vec 𝕋 n)) (kept : List Nat)
    (ids : Array Nat) : Array Nat :=
  (Array.ofFn fun k : Fin pZ.p => k).filterMap fun k =>
    if kept.any (fun l => if hl : l < pZ.h then pZ.E k ⟨l, hl⟩ != 0 else false) then ids[k.val]?
    else none

end codec

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
