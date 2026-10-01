import CORALean.Examples.Bench.NumberType

/-!
# `firststep`: the fields every record starts with

`format` is `IEEE`'s label, `p<p>` for a significand width (never `binary8` for `Dyadic 4`,
which is no format) and `decimal<f>` for fixed point; `NumberType`'s `metaFields` follow, an
`IEEE` format's parameters among them.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

def firstStepHead {𝕋 : Type} (ty format : String) (sig : Nat) (nt : NumberType 𝕋) :
    List (String × Json) :=
  [("type", Json.str ty), ("format", Json.str format), ("significand_bits", Lean.toJson sig)] ++
    nt.metaFields

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
