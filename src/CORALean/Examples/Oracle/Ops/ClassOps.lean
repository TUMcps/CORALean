import CORALean.Examples.Oracle.Ops.CapsuleOps
import CORALean.Examples.Oracle.Ops.ConZonotopeOps
import CORALean.Examples.Oracle.Ops.EllipsoidOps
import CORALean.Examples.Oracle.Ops.EmptySetOps
import CORALean.Examples.Oracle.Ops.FullspaceOps
import CORALean.Examples.Oracle.Ops.ConversionOps
import CORALean.Examples.Oracle.Ops.IntervalMatrixOps
import CORALean.Examples.Oracle.Ops.LinearSysOps
import CORALean.Examples.Oracle.Ops.MatZonotopeOps
import CORALean.Examples.Oracle.Ops.PolytopeOps
import CORALean.Examples.Oracle.Ops.SpecificationOps
import CORALean.Examples.Oracle.Ops.ZonoBundleOps

/-!
# The class prefixes of the further set classes

`handleClassOp cls name` routes `"<cls>.<name>"` to the class's handler file; `classOpNames` lists
every served name, for `ping` and for the unknown-op error.

## Inputs
* none

## Output
* the names served, or the response fields of an op
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every `"<cls>.<name>"` the further classes serve. -/
@[noinline]
def classOpNames : List String :=
  conZonotopeOpNames.map ("conZonotope." ++ ·) ++ zonoBundleOpNames.map ("zonoBundle." ++ ·) ++
  polytopeOpNames.map ("polytope." ++ ·) ++ ellipsoidOpNames.map ("ellipsoid." ++ ·) ++
  capsuleOpNames.map ("capsule." ++ ·) ++ emptySetOpNames.map ("emptySet." ++ ·) ++
  fullspaceOpNames.map ("fullspace." ++ ·) ++ intervalMatrixOpNames.map ("intervalMatrix." ++ ·) ++
  matZonotopeOpNames.map ("matZonotope." ++ ·) ++
  specificationOpNames.map ("specification." ++ ·) ++
  linearSysOpNames.map ("linearSys." ++ ·) ++ intervalConversionNames.map ("interval." ++ ·) ++
  zonotopeConversionNames.map ("zonotope." ++ ·)

/-- `"<cls>.<name>"` at the scalar `dops` names; `none` if the class does not serve it. -/
@[noinline, nospecialize]
def handleClassOp {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (dops : DtypeOps 𝕋) (cls name : String) (req : Json) :
    Option (Except String (List (String × Json))) :=
  match cls with
  | "conZonotope" => handleConZonotopeOp dops name req
  | "zonoBundle" => handleZonoBundleOp dops name req
  | "polytope" => handlePolytopeOp dops name req
  | "ellipsoid" => handleEllipsoidOp dops name req
  | "capsule" => handleCapsuleOp dops name req
  | "emptySet" => handleEmptySetOp dops name req
  | "fullspace" => handleFullspaceOp dops name req
  | "intervalMatrix" => handleIntervalMatrixOp dops name req
  | "matZonotope" => handleMatZonotopeOp dops name req
  | "linearSys" => handleLinearSysOp dops name req
  | "specification" => handleSpecificationOp dops name req
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
