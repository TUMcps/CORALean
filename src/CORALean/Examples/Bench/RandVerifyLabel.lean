/-!
# `randverify`: a number type's label

`dyadic<p>`, `binary16|32|64` (IEEE), `float` (hardware), `nearest` (binary64) or `nearest<p>`
(`Dyadic p` rounded to nearest) -- both unsound -- and `flint<p>`. `randTypeKind` gives the kind
(`dyadic`, `ieee`, `float`, `nearest`, `flint`) and the width `p` where the label has one, `none`
for a label that is no type.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- =====================================  MAIN DEFINITION  ====================================== --

def randTypeKind (label : String) : Option (String × Option Nat) :=
  let numeric (pre : String) : Option Nat :=
    if label.startsWith pre then (label.drop pre.length).toNat? else none
  match label with
  | "binary16" | "binary32" | "binary64" => some ("ieee", none)
  | "float" => some ("float", none)
  | "nearest" => some ("nearest", none)
  | _ =>
    match numeric "dyadic", numeric "nearest", numeric "flint" with
    | some p, _, _ => some ("dyadic", some p)
    | _, some p, _ => some ("nearest", some p)
    | _, _, some p => some ("flint", some p)
    | _, _, _ => none

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
