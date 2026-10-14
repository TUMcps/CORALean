import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Operations.ReduceCombastel
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
import CORALean.Examples.Oracle.Dtype

/-!
# The zonotope-to-zonotope ops: `mtimes`, `mtimesInterval`, `plus`, `plusBox`, `linComb`, `reduce`

Every result's `E` comes from the library's own sound float operation, reached
through the classes `Mtimes.mtimes`, `Plus.plus` and `LinComb.linComb`
(`ContSet/Zonotope/Float/Instances.lean`) -- nothing here re-rounds anything.

`plusBox` (alias `plusInterval`) is the one exception with no class of its own:
`Instances.lean` gives `Plus` only at two zonotopes, never at a zonotope and a
box. `Z ⊞ I` is instead `{Z with E := Z.E ⊞ I}`, `⊞` now `Interval`'s own sound
`Plus (Interval (Vec 𝕋 n)) (Vec ℝ n)` instance: since `construct Z = nominal Z +
Z.E` and `Z.E ⊞ I ⊇ Z.E + I` (`Interval.plus_outer`), `construct Z + I ⊆
construct {Z with E := Z.E ⊞ I}` -- an informal claim, not a theorem restated
here.

`reduce` goes around the `Reduce` class rather than through it: that instance is
fixed to Girard's rule (`Instances.lean`'s own `reduce Z o := Z.reduceGirard
o`), so a `method` choice calls `Zonotope.reduceGirard`/`.reduceCombastel`
directly, each with its own `_outer` theorem.
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

def handleMtimesInterval (dops : DtypeOps 𝕋) (req : Json) :
    Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let ⟨_, IM⟩ ← parseIntervalMatColsFixed dops.readExact dz.n (← field req "M")
  pure [("Z", printZonotope dops.showExact
    (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      IM dz.Z))]

def handlePlus (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let Z2 ← parseZonotopeFixed dops.readExact dz.n (← field req "Z2")
  pure [("Z", printZonotope dops.showExact (Plus.plus dz.Z Z2))]

/-- `plusBox`/`plusInterval`: see the module docstring for the enclosure argument. -/
def handlePlusBox (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let I ← parseIntervalVecFixed dops.readExact dz.n (← field req "I")
  pure [("Z", printZonotope dops.showExact { dz.Z with I_error := Plus.plus dz.Z.I_error I })]

def handleLinComb (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let Z2 ← parseZonotopeFixed dops.readExact dz.n (← field req "Z2")
  pure [("Z", printZonotope dops.showExact (LinComb.linComb dz.Z Z2))]

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
