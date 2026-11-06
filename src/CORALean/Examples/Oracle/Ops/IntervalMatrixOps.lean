import CORALean.ContDynamics.LinearSys.MatExp.Operations.DependentTermsFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
import CORALean.ContSet.Conversion.Float.Operations.Interval_to_MatPolytope
import CORALean.ContSet.Interval.Float.Operations.Basic
import CORALean.ContSet.Interval.Float.Operations.CenterBoxMat
import CORALean.ContSet.Interval.Float.Operations.ContainsMat
import CORALean.ContSet.Interval.Float.Operations.ExactSquare
import CORALean.ContSet.Interval.Float.Operations.InfNorm
import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.MatNorm
import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.MatPow
import CORALean.ContSet.Interval.Float.Operations.MatVolume
import CORALean.ContSet.Interval.Float.Operations.Powers
import CORALean.ContSet.Interval.Float.Operations.RadiusMat
import CORALean.ContSet.Interval.Float.Operations.Vec
import CORALean.ContSet.Zonotope.Float.Operations.OfIntervalMat
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Examples.Oracle.Ops.IntervalOps

/-!
# The interval-matrix ops: CORA's `intervalMatrix` methods

An interval matrix is `Interval (Mat 𝕋 m n)`, so these are adapters over the float definitions
`references/coverage/others/intervalMatrix.md` links. Operands are `IM`, `IM2` (`{"inf","sup"}`,
two matrices); a set result is `IM`, a matrix zonotope `mZ`, a matrix or scalar `value`, `V` the
list of vertex matrices with the error box `E`. `norm` takes `steps` (Newton steps of the
Frobenius root) and `type` (`1`, `inf`, `fro`). `expmInd` takes `maxOrder`. Not served: the
constructor, which is `interval.intervalMatrix`.

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

/-- An interval matrix of the already-known shape `r × c`. -/
private def aux_boxMatFixed (readD : String → ExactScalar → Except String 𝕋) (r c : Nat)
    (j : Json) :
    Except String (Interval (Mat 𝕋 r c)) := do
  let b ← parseBoxMat readD j
  if h : b.r = r ∧ b.c = c then pure (h.1 ▸ h.2 ▸ b.I)
  else throw s!"expected a {r}×{c} interval matrix, got {b.r}×{b.c}"

private def aux_set (dops : DtypeOps 𝕋) (name : String) {r c : Nat} (I : Interval (Mat 𝕋 r c)) :
    String × Json :=
  (name, printIntervalMat dops.showExact I)

/-- The square interval matrix in field `name`, as an `n × n` one. -/
private def aux_square (dops : DtypeOps 𝕋) (req : Json) (name : String) :
    Except String (Σ n : Nat, Interval (Mat 𝕋 n n)) := do
  let b ← parseBoxMat dops.readExact (← field req name)
  if h : b.c = b.r then pure ⟨b.r, h ▸ b.I⟩
  else throw s!"`{name}` must be square, not {b.r}×{b.c}"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intervalMatrix.vertices`: the `2^(m n)` corner matrices, `Interval.matPolytope`, at most
`2^20`. -/
def handleIntervalMatrixVertices (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "vertices" req ["IM"]
  let b ← parseBoxMat dops.readExact (← field req "IM")
  if b.r * b.c > 20 then
    throw s!"vertices: {b.r}×{b.c} entries give 2^{b.r * b.c} vertices, at most 2^20 are returned"
  let P := Interval.matPolytope b.I
  pure [("V", Json.arr (Array.ofFn fun l : Fin P.k => printMat dops.showExact (P.V l))),
    ("E", printIntervalMat dops.showExact P.I_error)]

/-- `intervalMatrix.representsa`: of the vectorised matrix, `type` one of `emptySet`, `point`,
`origin`. -/
def handleIntervalMatrixRepresentsa (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "representsa" req ["IM", "type", "tol"]
  checkTol "representsa" req
  let b ← parseBoxMat dops.readExact (← field req "IM")
  match ← strField req "type" with
  | "emptySet" => valueBool (Interval.representsa_emptySet b.I.vec)
  | "point" => valueBool (Interval.representsa_point b.I.vec)
  | "origin" => valueBool (Interval.representsa_origin b.I.vec)
  | t => throw s!"representsa: `type` must be emptySet, point or origin, not `{t}`"

/-- Every op of this file, without the `intervalMatrix.` prefix. -/
def intervalMatrixOpNames : List String :=
  [ "abs", "center", "contains", "dependentTerms", "exactSquare", "expmInd", "infNorm", "infimum",
    "matZonotope", "mpower", "mtimes", "norm", "plus", "powers", "rad", "representsa", "supremum",
    "vertices", "volume" ]

/-- `op` of `intervalMatrix.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleIntervalMatrixOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "abs" => some (do
      checkFields op req ["IM"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      pure [("value", printMat dops.showExact (Interval.magnitudeMat b.I))])
  | "center" => some (do
      checkFields op req ["IM"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      pure [aux_set dops "IM" (Interval.centerBoxMat b.I)])
  -- the arms from `contains` on
  | "contains" => some (do
      checkFields op req ["IM", "M", "tol"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      let ⟨r, M⟩ ← parseMatColsFixed dops.readExact b.c (← field req "M")
      let tol ← match fieldOpt req "tol" with
        | none => pure FloatOps.zero
        | some _ => dops.readExact "tol" (← scalarField req "tol")
      if h : r = b.r then pure [("contains", Json.bool (Interval.containsMat b.I (h ▸ M) tol))]
      else throw s!"contains: `M` has {r} rows, the interval matrix has {b.r}")
  | "dependentTerms" => some (do
      checkFields op req ["IM", "r"]
      let ⟨_, A⟩ ← aux_square dops req "IM"
      let r ← dops.readExact "r" (← scalarField req "r")
      let t := MatExp.dependentTerms A r
      pure [aux_set dops "intSq" t.intSq, aux_set dops "intH" t.intH])
  -- the arms from `exactSquare` on
  | "exactSquare" => some (do
      checkFields op req ["IM"]
      let ⟨_, A⟩ ← aux_square dops req "IM"
      pure [aux_set dops "IM" (Interval.exactSquare A)])
  -- `expmInd`: `MatExp.expIntervalEnclosure` at `maxOrder`, coarser than CORA's remainder
  | "expmInd" => some (do
      checkFields op req ["IM", "maxOrder"]
      let ⟨_, A⟩ ← aux_square dops req "IM"
      pure [aux_set dops "IM" (MatExp.expIntervalEnclosure A (← natField req "maxOrder"))])
  | "infNorm" => some (do
      checkFields op req ["IM"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      valueScalar dops.showExact (Interval.infNorm b.I))
  | "infimum" => some (do
      checkFields op req ["IM"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      pure [("value", printMat dops.showExact (Interval.infimum b.I))])
  -- the arms from `supremum` on
  | "supremum" => some (do
      checkFields op req ["IM"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      pure [("value", printMat dops.showExact (Interval.supremum b.I))])
  | "matZonotope" => some (do
      checkFields op req ["IM"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      pure [("mZ", printMatZonotope dops.showExact (Zonotope.ofIntervalMat b.I))])
  | "mpower" => some (do
      checkFields op req ["IM", "exponent"]
      let ⟨_, A⟩ ← aux_square dops req "IM"
      pure [aux_set dops "IM" (Interval.matPow A (← natField req "exponent"))])
  -- the arms from `mtimes` on
  | "mtimes" => some (do
      checkFields op req ["IM", "IM2"]
      let a ← parseBoxMat dops.readExact (← field req "IM")
      let b ← parseBoxMat dops.readExact (← field req "IM2")
      if h : b.r = a.c then
        pure [aux_set dops "IM" (Interval.matMul a.I (h ▸ b.I))]
      else throw s!"mtimes: the factors are {a.r}×{a.c} and {b.r}×{b.c}")
  | "norm" => some (do
      checkFields op req ["IM", "type", "steps"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      let steps ← natField req "steps"
      valueScalar dops.showExact (Interval.matNorm steps (← normTypeField op req) b.I))
  -- the arms from `plus` on
  | "plus" => some (do
      checkFields op req ["IM", "IM2"]
      let a ← parseBoxMat dops.readExact (← field req "IM")
      let b ← aux_boxMatFixed dops.readExact a.r a.c (← field req "IM2")
      pure [aux_set dops "IM" (Interval.matPlus a.I b)])
  | "powers" => some (do
      checkFields op req ["IM", "IM2", "k"]
      let ⟨n, A⟩ ← aux_square dops req "IM"
      let P ← aux_boxMatFixed dops.readExact n n (← field req "IM2")
      pure [aux_set dops "IM" (Interval.powers A P (← natField req "k"))])
  -- the arms from `rad` on
  | "rad" => some (do
      checkFields op req ["IM"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      pure [("value", printMat dops.showExact (Interval.radiusMat b.I))])
  | "representsa" => some (handleIntervalMatrixRepresentsa dops req)
  | "vertices" => some (handleIntervalMatrixVertices dops req)
  | "volume" => some (do
      checkFields op req ["IM"]
      let b ← parseBoxMat dops.readExact (← field req "IM")
      valueScalar dops.showExact (Interval.matVolume b.I))
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
