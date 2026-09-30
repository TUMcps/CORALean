import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Lean.Data.Json.FromToJson

/-!
# What a run says about its own scalar

`FloatOps` says how a scalar computes and nothing about what it is. A run's output also needs to
say which number type it ran at, honestly: `Dyadic 11` is a significand width with an unbounded
exponent, not binary16, and only `--type ieee` is a format. And where a format has a largest
finite number, it needs to say which stored values are past it. `NumberType` carries both into
the writers, beside the parameters that go into `meta` as they are.

Every field defaults to saying nothing, so a call site that passes none reads as before.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- ========================================  MAIN TYPE  ========================================= --

/-- `description` for `meta.number_type` and the log line, `overflows` where the type has a
range to leave, and `params` copied into `meta` verbatim. -/
structure NumberType (𝕋 : Type) where
  description : String := ""
  overflows : Option (𝕋 → Bool) := none
  params : List (String × Json) := []

/-- `meta.number_type`, where there is a description to give. -/
def NumberType.metaFields {𝕋 : Type} (nt : NumberType 𝕋) : List (String × Json) :=
  (if nt.description = "" then [] else [("number_type", Json.str nt.description)]) ++ nt.params

/-- What `Dyadic sig` is, said so that its `--format` label cannot be read as a format: `p=16`
is the paper's name for the width `formatToPrec` maps `binary16` to, and nothing more. -/
def dyadicDescription (label : String) (sig : Nat) : String :=
  let p := match label with
    | "binary64" => " p=64" | "binary32" => " p=32" | "binary16" => " p=16"
    | "binary8" => " p=8" | "binary4" => " p=4" | _ => ""
  s!"dyadic{p} ({sig}-bit significand, unbounded exponent)"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
