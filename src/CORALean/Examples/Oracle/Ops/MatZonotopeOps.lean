import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosureFloat
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_MatPolytope
import CORALean.ContSet.Interval.Float.Operations.MatNorm
import CORALean.ContSet.Zonotope.Float.Operations.MatMul
import CORALean.ContSet.Zonotope.Float.Operations.MatNorm
import CORALean.ContSet.Zonotope.Float.Operations.MatPlus
import CORALean.ContSet.Zonotope.Float.Operations.Mpower
import CORALean.ContSet.Zonotope.Float.Operations.Powers
import CORALean.ContSet.Zonotope.Float.Operations.Transpose
import CORALean.ContSet.Zonotope.Float.Operations.Vec
import CORALean.ContSet.Zonotope.Float.Operations.RepresentsaOrigin
import CORALean.ContSet.Zonotope.Float.Operations.RepresentsaPoint
import CORALean.Examples.Oracle.Ops.IntervalMatrixOps

/-!
# The matrix-zonotope ops: CORA's `matZonotope` methods

A matrix zonotope is `Zonotope (Mat 𝕋 m n)` and has no class of its own, so these are the
adapters over the float definitions `references/coverage/others/matZonotope.md` links. Operands
are `mZ`, `mZ2` (`{"c","G":[matrix, ...],"E"}`, `E` an interval matrix, see `SetCodec.lean`); a
set result is `mZ`, an interval matrix `IM`, a vector zonotope `Z`, a matrix or a scalar `value`,
`V` the list of vertex matrices with the error box `E`. `steps` is the tuning of `norm`, `type`
is `1`, `inf` or `fro`. Indices are 0-based; a field an op does not list is refused by name.
`expm` and `expmInd` take `maxOrder`. Not served (no float definition): `contains`,
`dependentTerms`, `expmMixed`, `expmOneParam`, the constructor.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* response fields or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private def aux_set (dops : DtypeOps 𝕋) {r c : Nat} (Z : Zonotope (Mat 𝕋 r c)) : String × Json :=
  ("mZ", printMatZonotope dops.showExact Z)

/-- A matrix zonotope of the already-known shape `r × c`. -/
private def aux_fixed (dops : DtypeOps 𝕋) (r c : Nat) (j : Json) :
    Except String (Zonotope (Mat 𝕋 r c)) := do
  let d ← parseMatZonotope dops.readExact j
  if h : d.r = r ∧ d.c = c then pure (h.1 ▸ h.2 ▸ d.Z)
  else throw s!"expected a {r}×{c} matrix zonotope, got {d.r}×{d.c}"

/-- The square matrix zonotope in field `name`. -/
private def aux_square (dops : DtypeOps 𝕋) (req : Json) (name : String) :
    Except String (Σ n : Nat, Zonotope (Mat 𝕋 n n)) := do
  let d ← parseMatZonotope dops.readExact (← field req name)
  if h : d.c = d.r then pure ⟨d.r, h ▸ d.Z⟩
  else throw s!"`{name}` must be square, not {d.r}×{d.c}"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `matZonotope.vertices`: the corner matrices, `Zonotope.matPolytope`, at most `2^20`. -/
def handleMatZonotopeVertices (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "vertices" req ["mZ"]
  let d ← parseMatZonotope dops.readExact (← field req "mZ")
  if d.Z.h > 20 then
    throw s!"vertices: {d.Z.h} generators give 2^{d.Z.h} corners, at most 2^20 are returned"
  let P := Zonotope.matPolytope d.Z
  pure [("V", Json.arr (Array.ofFn fun l : Fin P.k => printMat dops.showExact (P.V l))),
    ("E", printIntervalMat dops.showExact P.I_error)]

/-- `matZonotope.representsa`: of the vectorised matrix zonotope, `type` `point` or `origin`. -/
def handleMatZonotopeRepresentsa (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "representsa" req ["mZ", "type", "tol"]
  checkTol "representsa" req
  let d ← parseMatZonotope dops.readExact (← field req "mZ")
  match ← strField req "type" with
  | "point" => valueBool (Zonotope.representsa_point (Zonotope.vec d.Z))
  | "origin" => valueBool (Zonotope.representsa_origin (Zonotope.vec d.Z))
  | t => throw s!"representsa: `type` must be point or origin, not `{t}`"

/-- Every op of this file, without the `matZonotope.` prefix. -/
def matZonotopeOpNames : List String :=
  [ "center", "expm", "expmInd", "intervalMatrix", "mpower", "mtimes", "norm", "plus", "powers",
    "representsa",
    "transpose", "vertices", "zonotope" ]

/-- `op` of `matZonotope.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleMatZonotopeOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "center" => some (do
      checkFields op req ["mZ"]
      let d ← parseMatZonotope dops.readExact (← field req "mZ")
      pure [("value", printMat dops.showExact d.Z.c)])
  | "expm" | "expmInd" => some (do
      checkFields op req ["mZ", "maxOrder"]
      let ⟨_, Z⟩ ← aux_square dops req "mZ"
      pure [aux_set dops (MatExp.expMatZonoEnclosure Z (← natField req "maxOrder"))])
  | "intervalMatrix" => some (do
      checkFields op req ["mZ"]
      let d ← parseMatZonotope dops.readExact (← field req "mZ")
      pure [("IM", printIntervalMat dops.showExact (Zonotope.matInterval d.Z))])
  -- the arms from `mpower` on
  | "mpower" => some (do
      checkFields op req ["mZ", "exponent"]
      let ⟨_, Z⟩ ← aux_square dops req "mZ"
      pure [aux_set dops (Zonotope.mpower Z (← natField req "exponent"))])
  | "mtimes" => some (do
      checkFields op req ["mZ", "mZ2"]
      let a ← parseMatZonotope dops.readExact (← field req "mZ")
      let b ← parseMatZonotope dops.readExact (← field req "mZ2")
      if h : b.r = a.c then pure [aux_set dops (Zonotope.matMul a.Z (h ▸ b.Z))]
      else throw s!"mtimes: the factors are {a.r}×{a.c} and {b.r}×{b.c}")
  -- the arms from `norm` on
  | "norm" => some (do
      checkFields op req ["mZ", "type", "steps"]
      let d ← parseMatZonotope dops.readExact (← field req "mZ")
      valueScalar dops.showExact
        (Zonotope.matNorm (← natField req "steps") (← normTypeField op req) d.Z))
  | "plus" => some (do
      checkFields op req ["mZ", "mZ2"]
      let a ← parseMatZonotope dops.readExact (← field req "mZ")
      let b ← aux_fixed dops a.r a.c (← field req "mZ2")
      pure [aux_set dops (Zonotope.matPlus a.Z b)])
  -- the arms from `powers` on
  | "powers" => some (do
      checkFields op req ["mZ", "mZ2", "k"]
      let ⟨n, Z⟩ ← aux_square dops req "mZ"
      let P ← aux_fixed dops n n (← field req "mZ2")
      pure [aux_set dops (Zonotope.powers Z P (← natField req "k"))])
  | "representsa" => some (handleMatZonotopeRepresentsa dops req)
  | "transpose" => some (do
      checkFields op req ["mZ"]
      let d ← parseMatZonotope dops.readExact (← field req "mZ")
      pure [aux_set dops (Zonotope.transpose d.Z)])
  -- the arms from `vertices` on
  | "vertices" => some (handleMatZonotopeVertices dops req)
  | "zonotope" => some (do
      checkFields op req ["mZ"]
      let d ← parseMatZonotope dops.readExact (← field req "mZ")
      pure [("Z", printZonotope dops.showExact (Zonotope.vec d.Z))])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
