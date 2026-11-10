import CORALean.Examples.Oracle.Dtype

/-!
# What every class's op handlers share

`checkFields` is the one refusal of an option CORALean does not model: a request field that the op
does not list is an error naming it, never silently ignored, so a client that sends CORA's
`method`, `tol` or `cert` learns at once that the float definition answers none of them.
`checkTol` accepts the CORA argument `tol` only at `0`, which is what the definitions that take
no tolerance compute. The readers fetch one typed field (a scalar of the dtype, a natural number,
a list of 0-based indices); indices on the wire are 0-based, as in Lean and in C++.

## Inputs
* `op` – the op's name, for messages
* `req` – the request
* `allowed` – the field names the op accepts besides `op`, `dtype` and `id`

## Output
* `()` or an error naming the field
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

/-- The gate of an op whose soundness rests on an unproved `Encloses` hypothesis: served at
`nearest`, refused at a guaranteed dtype; `check-axioms.lean` requires it of such handlers. -/
def DtypeOps.requireUnguaranteed {𝕋 : Type} [FloatOps 𝕋] (dops : DtypeOps 𝕋) (op : String) :
    Except String Unit :=
  if dops.guaranteed then
    throw s!"{op}: not served at the guaranteed dtype `{dops.label}`: its soundness rests on a \
      hypothesis that is not proved in Lean (the dynamics' model encloses the system); \
      use dtype `nearest`"
  else pure ()

/-- A result of a handler: the response fields, or an error message. -/
abbrev Resp : Type := Except String (List (String × Json))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Refuses a field of `req` that `op` does not list, naming it and what the op accepts. -/
def checkFields (op : String) (req : Json) (allowed : List String) : Except String Unit := do
  let keys : List String :=
    match req.getObj? with
    | .ok kvs => kvs.toList.map (·.1)
    | .error _ => []
  match keys.find? fun k => !(["op", "dtype", "id"] ++ allowed).contains k with
  | some k =>
    throw s!"{op}: option `{k}` is not modeled by CORALean's float {op} \
      (it accepts {String.intercalate ", " allowed})"
  | none => pure ()

/-- Accepts CORA's `tol` argument at `0` only, for a definition that takes no tolerance. -/
def checkTol (op : String) (req : Json) : Except String Unit := do
  match fieldOpt req "tol" with
  | none => pure ()
  | some j =>
    match j.getNum? with
    | .ok n => if n.mantissa = 0 then pure () else
        throw s!"{op}: `tol` must be 0, CORALean's float {op} takes no tolerance"
    | .error _ => throw s!"{op}: `tol` must be a number, not {kindOf j}"

/-- `req`'s field `name`, an array of naturals. -/
def natArrField (req : Json) (name : String) : Except String (Array Nat) := do
  (← arrField req name).mapM fun v =>
    match v.getNat? with
    | .ok k => pure k
    | .error _ => throw s!"field `{name}` must be an array of nonnegative integers"

/-- `req`'s field `name`, an array of 0-based indices below `n`, as a function out of `Fin m`. -/
def indexArrField (req : Json) (name : String) (n : Nat) :
    Except String (Σ m : Nat, Fin m → Fin n) := do
  let a ← natArrField req name
  if h : ∀ i : Fin a.size, a[i] < n then
    pure ⟨a.size, fun i => ⟨a[i], h i⟩⟩
  else throw s!"field `{name}`: every index must be below {n} (indices are 0-based)"

/-- `req`'s field `name`, a 0-based index below `n`. -/
def indexField (req : Json) (name : String) (n : Nat) : Except String (Fin n) := do
  let k ← natField req name
  if h : k < n then pure ⟨k, h⟩
  else throw s!"field `{name}` = {k} is out of range, the dimension is {n} (indices are 0-based)"

/-- The entries of the `h × n` matrix `H`, computed once, row by row. -/
def tableOf {𝕋 : Type} {h n : Nat} (H : Fin h → Fin n → 𝕋) : Array (Array 𝕋) :=
  Array.ofFn fun j : Fin h => Array.ofFn fun i : Fin n => H j i

/-- Entry `(j, i)` of a `tableOf` table, `d` outside it. -/
def tableGet {𝕋 : Type} {h n : Nat} (d : 𝕋) (a : Array (Array 𝕋)) (j : Fin h) (i : Fin n) : 𝕋 :=
  (a.getD j.val #[]).getD i.val d

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
