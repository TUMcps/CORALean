import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Operations.ReduceCombastel
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
import CORALean.Examples.Oracle.Dtype

/-!
# The zonotope-to-zonotope ops: `mtimes`, `mtimesInterval`, `plus`, `plusBox`, `linComb`, `reduce`

Every result's `E` comes from the library's own sound float operation, reached through the classes
`Mtimes.mtimes`, `Plus.plus` and `LinComb.linComb`; nothing here re-rounds anything. `plusBox`
(alias `plusInterval`) is the one exception with no class of its own: `Z ⊞ I` is
`{Z with E := Z.E ⊞ I}`, `⊞` `Interval`'s own sound `Plus` instance; since
`construct Z = nominal Z + Z.E` and `Z.E ⊞ I ⊇ Z.E + I` (`Interval.plus_outer`),
`construct Z + I ⊆ construct {Z with E := Z.E ⊞ I}`, an informal claim. `reduce` goes around the
`Reduce` class, fixed to Girard's rule: a `method` choice calls
`Zonotope.reduceGirard`/`.reduceCombastel` directly, each with its own `_outer` theorem.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* response fields or an error message
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def handleMtimes (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let ⟨_, M⟩ ← parseMatColsFixed dops.readExact dz.n (← field req "M")
  pure [("Z", printZonotope dops.showExact
    (Mtimes.mtimes (S := 𝒵[𝕋]) M dz.Z))]

/-- Handles `mtimesInterval`: the zonotope `Z` multiplied by an interval matrix. -/
def handleMtimesInterval (dops : DtypeOps 𝕋) (req : Json) :
    Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let ⟨_, IM⟩ ← parseIntervalMatColsFixed dops.readExact dz.n (← field req "M")
  pure [("Z", printZonotope dops.showExact
    (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      IM dz.Z))]

/-- Handles `plus`: the Minkowski sum of `Z` and `Z2`. -/
def handlePlus (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let Z2 ← parseZonotopeFixed dops.readExact dz.n (← field req "Z2")
  pure [("Z", printZonotope dops.showExact (Plus.plus dz.Z Z2))]

/-- `plusBox`/`plusInterval`: see the module docstring for the enclosure argument. -/
def handlePlusBox (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let I ← parseIntervalVecFixed dops.readExact dz.n (← field req "I")
  pure [("Z", printZonotope dops.showExact { dz.Z with I_error := Plus.plus dz.Z.I_error I })]

/-- Handles `linComb`: the linear combination of `Z` and `Z2`. -/
def handleLinComb (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let Z2 ← parseZonotopeFixed dops.readExact dz.n (← field req "Z2")
  pure [("Z", printZonotope dops.showExact (LinComb.linComb dz.Z Z2))]

/-- Handles `reduce`: reduces `Z` to the given order by the Girard or the Combastel method. -/
def handleReduce (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let order ← natField req "order"
  let method ← strField req "method"
  let Z' ← match method with
    | "girard" => pure (Zonotope.reduceGirard dz.Z order)
    | "combastel" => pure (Zonotope.reduceCombastel dz.Z order)
    | m => throw s!"reduce: `method` must be `girard` or `combastel`, not `{m}`"
  pure [("Z", printZonotope dops.showExact Z')]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
