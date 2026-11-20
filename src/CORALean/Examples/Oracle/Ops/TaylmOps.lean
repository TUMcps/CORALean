import CORALean.ContSet.Taylm.Float.Operations.BoundsMono
import CORALean.ContSet.Taylm.Float.Operations.Basic
import CORALean.ContSet.Taylm.Float.Operations.PlusScalar
import CORALean.ContSet.Taylm.Float.Operations.PowBinary
import CORALean.ContSet.Taylm.Float.Operations.Scale
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The Taylor-model ops: CORA's `taylm` arithmetic as CORA.cpp computes it

Adapters over the float definitions `references/coverage/contSet/taylm.md` links, each one
CORA.cpp's `Taylm` method: the terms sorted by their exponents with equal monomials merged, as its
ordered map keeps them. A model is `{"vars", "maxOrder", "terms": [{"c", "e"}], "rem"}`, its terms
taken in the order given; a response adds the error box `"Ierr"` (zero at nearest). Served: `plus`,
`minus` (a model `Q` or a number `s`), `uminus`, `uplus`, `times` (`Q` at the request's `maxOrder`,
or `s`), `power` (`k`) and `interval` (CORA's method `'int'`).

## Inputs
* none

## Output
* the names of the ops served, or the response fields of an op
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A Taylor model of the number of variables read off the request. -/
private structure DynTaylm (𝕋 : Type) [FloatOps 𝕋] where
  n : Nat
  T : Taylm 𝕋 n

/-- The interval `{"inf", "sup"}` of scalars in field `name`. -/
private def aux_scalarInterval (dops : DtypeOps 𝕋) (j : Json) (name : String) :
    Except String (Interval 𝕋) := do
  let I ← field j name
  pure ⟨← dops.readExact name (← scalarField I "inf"),
    ← dops.readExact name (← scalarField I "sup")⟩

/-- The model `j` of `n` variables. -/
private def aux_parseFixed (dops : DtypeOps 𝕋) (n : Nat) (j : Json) :
    Except String (Taylm 𝕋 n) := do
  let terms ← (← arrField j "terms").toList.mapM fun t => do
    let c ← dops.readExact "c" (← scalarField t "c")
    let e ← natArrField t "e"
    if h : e.size = n then pure (c, fun k : Fin n => e[k.val]'(h ▸ k.isLt))
    else throw s!"a term has {e.size} exponents, the model {n} variables"
  pure ⟨terms, ← aux_scalarInterval dops j "rem", ⟨FloatOps.zero, FloatOps.zero⟩,
    ← natField j "maxOrder"⟩

/-- The model `j`, its number of variables from `vars`. -/
private def aux_parse (dops : DtypeOps 𝕋) (j : Json) : Except String (DynTaylm 𝕋) := do
  let n ← natField j "vars"
  pure ⟨n, ← aux_parseFixed dops n j⟩

/-- A model as the response. -/
private def aux_print (dops : DtypeOps 𝕋) {n : Nat} (T : Taylm 𝕋 n) : List (String × Json) :=
  let s := fun x : 𝕋 => Json.str (dops.showExact x)
  let I := fun J : Interval 𝕋 => Json.mkObj [("inf", s J.inf), ("sup", s J.sup)]
  [("T", Json.mkObj [("vars", Lean.toJson n), ("maxOrder", Lean.toJson T.maxOrder),
    ("terms", Json.arr (T.terms.toArray.map fun a => Json.mkObj
      [("c", s a.1), ("e", Lean.toJson (Array.ofFn a.2))])),
    ("rem", I T.rem), ("Ierr", I T.I_error)])]

/-- The second operand: a model `Q` of the same variables, or a number `s`. -/
private def aux_operand (dops : DtypeOps 𝕋) (op : String) (n : Nat) (req : Json) :
    Except String (Taylm 𝕋 n ⊕ 𝕋) :=
  match fieldOpt req "Q", fieldOpt req "s" with
  | some q, none => do
    let m ← natField q "vars"
    if m ≠ n then throw s!"{op}: the models have {n} and {m} variables"
    pure (.inl (← aux_parseFixed dops n q))
  | none, some _ => do pure (.inr (← dops.readExact "s" (← scalarField req "s")))
  | _, _ => throw s!"{op}: needs exactly one of `Q` and `s`"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every op of `taylm.`, without the prefix. -/
def taylmOpNames : List String :=
  ["plus", "minus", "uminus", "uplus", "times", "power", "interval"]

/-- `op` of `taylm.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleTaylmOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "plus" => some (do
    checkFields op req ["T", "Q", "s"]
    let d ← aux_parse dops (← field req "T")
    match ← aux_operand dops op d.n req with
    | .inl Q => pure (aux_print dops (d.T.plusMerged Q))
    | .inr s => pure (aux_print dops (d.T.plusScalar s)))
  | "minus" => some (do
    checkFields op req ["T", "Q", "s"]
    let d ← aux_parse dops (← field req "T")
    match ← aux_operand dops op d.n req with
    | .inl Q => pure (aux_print dops (d.T.minusMerged Q))
    | .inr s => pure (aux_print dops (d.T.plusScalar (FloatOps.neg s))))
  -- the negation and the model itself
  | "uminus" => some (do
    checkFields op req ["T"]
    let d ← aux_parse dops (← field req "T")
    pure (aux_print dops d.T.uminus))
  | "uplus" => some (do
    checkFields op req ["T"]
    let d ← aux_parse dops (← field req "T")
    pure (aux_print dops d.T.uplus))
  -- the product with a model needs the order it is truncated at
  | "times" => some (do
    checkFields op req ["T", "Q", "s", "maxOrder"]
    let d ← aux_parse dops (← field req "T")
    match ← aux_operand dops op d.n req with
    | .inl Q => pure (aux_print dops (Taylm.timesMerged (← natField req "maxOrder") d.T Q))
    | .inr s =>
      if (fieldOpt req "maxOrder").isSome then throw "times: `maxOrder` goes with `Q` only"
      pure (aux_print dops (d.T.scale s)))
  | "power" => some (do
    checkFields op req ["T", "k"]
    let d ← aux_parse dops (← field req "T")
    pure (aux_print dops (d.T.powBinary (← natField req "k"))))
  | "interval" => some (do
    checkFields op req ["T"]
    let d ← aux_parse dops (← field req "T")
    let B := d.T.boundsMono
    let I : Interval (Vec 𝕋 1) := ⟨fun _ => B.inf, fun _ => B.sup⟩
    pure [("I", printIntervalVec dops.showExact I)])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
