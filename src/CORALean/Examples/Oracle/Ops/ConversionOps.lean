import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Capsule
import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Ellipsoid
import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Ellipsoid
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
import CORALean.ContSet.Zonotope.Float.Operations.MatZonotope
import CORALean.Examples.Oracle.Ops.PolyZonotopeOps
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# Conversions out of the box and the zonotope

`interval.<class>` and `zonotope.<class>` for the classes that now have a wire format, adapters
over the conversions `references/coverage/contSet/interval.md` and `zonotope.md` link. A box is
`I`, a zonotope `Z`; a result is a polytope `P`, a constrained zonotope `cZ`, a bundle `zB`, a
capsule `C` or an ellipsoid `E`. The tuning the conversion takes and CORA has no argument for is
required: `k` (Newton steps) for `capsule`, `sigma` (the radius scale) for `ellipsoid`, `p` (steps
of the facet enumeration) for the zonotope `polytope`, which needs `n ≥ 1`.

## Inputs
* none

## Output
* the names served, or the response fields of an op
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   07-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A scalar field read exactly into the dtype. -/
private def aux_scalar (dops : DtypeOps 𝕋) (req : Json) (name : String) : Except String 𝕋 := do
  dops.readExact name (← scalarField req name)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The conversions of the box, without the `interval.` prefix. -/
def intervalConversionNames : List String :=
  [ "polytope", "conZonotope", "zonoBundle", "capsule", "ellipsoid", "polyZonotope" ]

/-- The conversions of the zonotope, without the `zonotope.` prefix. -/
def zonotopeConversionNames : List String :=
  [ "polytope", "conZonotope", "zonoBundle", "capsule", "ellipsoid", "matZonotope",
    "polyZonotope" ]

/-- `interval.<class>`: `I` converted. -/
def handleIntervalConversion (dops : DtypeOps 𝕋) (op : String) (req : Json) : Resp := do
  if op = "polyZonotope" then return ← handleIntervalPolyZonotope dops req
  let tuning := match op with
    | "capsule" => ["k"]
    | "ellipsoid" => ["sigma"]
    | _ => []
  checkFields op req ("I" :: tuning)
  let b ← parseBox dops.readExact (← field req "I")
  match op with
  | "polytope" => pure [("P", printHPolytope dops.showExact (Interval.hPolytope b.I))]
  | "conZonotope" => pure [("cZ", printConZonotope dops.showExact (Interval.conZonotope b.I))]
  | "zonoBundle" => pure [("zB", printZonoBundle dops.showExact (Interval.zonoBundle b.I))]
  | "capsule" =>
    pure [("C", printCapsule dops.showExact (Interval.capsule (← natField req "k") b.I))]
  | _ =>
    let σ ← aux_scalar dops req "sigma"
    pure [("E", printEllipsoid dops.showExact (Interval.ellipsoid b.I σ))]

/-- `zonotope.<class>`: `Z` converted. -/
def handleZonotopeConversion (dops : DtypeOps 𝕋) (op : String) (req : Json) : Resp := do
  if op = "polyZonotope" then return ← handleZonotopePolyZonotope dops req
  let tuning := match op with
    | "capsule" => ["k"]
    | "ellipsoid" => ["sigma"]
    | "polytope" => ["p"]
    | _ => []
  checkFields op req ("Z" :: tuning)
  let d ← parseZonotope dops.readExact (← field req "Z")
  match op with
  | "conZonotope" => pure [("cZ", printConZonotope dops.showExact (Zonotope.conZonotope d.Z))]
  | "zonoBundle" => pure [("zB", printZonoBundle dops.showExact (Zonotope.zonoBundle d.Z))]
  | "matZonotope" => pure [("mZ", printMatZonotope dops.showExact (Zonotope.matZonotope d.Z))]
  | "capsule" =>
    pure [("C", printCapsule dops.showExact (Zonotope.capsule (← natField req "k") d.Z))]
  | "ellipsoid" =>
    let σ ← aux_scalar dops req "sigma"
    pure [("E", printEllipsoid dops.showExact (Zonotope.ellipsoid d.Z σ))]
  | _ =>
    -- the facets of a zonotope in `m + 1` dimensions
    match hn : d.n with
    | 0 => throw "polytope: CORA's facet enumeration needs at least one dimension"
    | m + 1 =>
      let Z : Zonotope (Vec 𝕋 (m + 1)) := cast (by rw [hn]) d.Z
      pure [("P", printHPolytope dops.showExact
        (Zonotope.hPolytopeFacets (← natField req "p") Z))]

end

/-- `cls.op` of the box and the zonotope, run; `none` for a name that is not a conversion. -/
@[noinline, nospecialize]
def handleConversionOp {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (dops : DtypeOps 𝕋) (cls op : String) (req : Json) : Option Resp :=
  if cls = "interval" && intervalConversionNames.contains op then
    some (handleIntervalConversion dops op req)
  else if cls = "zonotope" && zonotopeConversionNames.contains op then
    some (handleZonotopeConversion dops op req)
  else none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
