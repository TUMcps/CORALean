import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.Examples.Bench.FirstStepRat
import CORALean.Global.Float.ToRat
import CORALean.Examples.Bench.NumberType
import Lean.Data.Json

/-!
# `firststep`: a zonotope as exact rationals

`ToRat.toRat` decodes every stored scalar exactly, so the output loses nothing a plot could
want: each scalar is `{"num": "...", "den": "..."}`, both decimal strings, `den > 0`. A scalar
that `nonFinite` flags (a value past an `IEEE` format's range, a `NaN`) is `null`, there being
no rational to give. The shape is the one `Output.stepJson` gives `sets_ti`: `c`, `G` as `n`
rows of `h`, and `E` with `inf` and `sup`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def aux_scalarRat (nonFinite : 𝕋 → Bool) (x : 𝕋) : Json :=
  if nonFinite x then Json.null else ratJson (ToRat.toRat x)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z`'s centre, generators and error box as exact rationals. -/
def zonotopeRatJson (nonFinite : 𝕋 → Bool) (Z : Zonotope (Vec 𝕋 2)) : Json :=
  let s := aux_scalarRat nonFinite
  Json.mkObj
    [ ("c", Json.arr (Array.ofFn fun i => s (Z.c i))),
      ("G", Json.arr (Array.ofFn fun i => Json.arr (Array.ofFn fun j => s (Z.G j i)))),
      ("E", Json.mkObj
        [ ("inf", Json.arr (Array.ofFn fun i => s (Z.E.inf i))),
          ("sup", Json.arr (Array.ofFn fun i => s (Z.E.sup i))) ]) ]

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
