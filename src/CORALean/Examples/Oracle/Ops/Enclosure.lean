import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError
import CORALean.ContSet.Zonotope.Float.Operations.Materialise
import CORALean.ContSet.Zonotope.Float.Theorems.Basic
import CORALean.Examples.Oracle.Dtype
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# `"interval"` and `"enclosure"`

`"interval"` is `Zonotope.interval`, the library's own box hull, sound by
`Zonotope.interval_contains`. `"enclosure"` asks for a zonotope enclosing `Z` with `E` exactly
`[0, 0]`. `Zonotope.absorbError` (`absorbError_outer`) moves the box into `n` generators about its
midpoint but leaves a residual `[lo_i, hi_i]` per row; this folds that residual too, without
rounding: each row with `[lo_i, hi_i] ≠ [0, 0]` gets one more generator `r_i · e_i`,
`r_i := maximum (neg lo_i) hi_i`, exact in every `FloatOps`, then `E := [0, 0]`. Soundness:
`e_i ∈ [lo_i, hi_i] ⊆ [-r_i, r_i]`; an informal claim, not a theorem restated here. A row already
`[0, 0]` gets no generator.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `x` is exactly `FloatOps.zero` -- `showExact`'s own normal form makes this a string
comparison, needing no `DecidableEq 𝕋`. -/
private def aux_isZeroT (dops : DtypeOps 𝕋) (x : 𝕋) : Bool :=
  dops.showExact x = dops.showExact FloatOps.zero


-- =====================================  MAIN DEFINITION  ====================================== --

def handleInterval (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  pure [("interval", printIntervalVec dops.showExact (Zonotope.interval dz.Z))]

/-- `Zp`'s residual box, row `i`, folded into a generator radius `r_i := maximum (neg lo_i)
hi_i` -- see the module docstring for why `[lo_i,hi_i] ⊆ [-r_i,r_i]`. `none` at a row already
`[0,0]`, so a zero generator is never appended. -/
private def aux_foldRow {n : ℕ} (dops : DtypeOps 𝕋) (Zp : Zonotope (Vec 𝕋 n)) (i : Fin n) :
    Option (Fin n × 𝕋) :=
  let r := FloatOps.maximum (FloatOps.neg (Zp.I_error.inf i)) (Zp.I_error.sup i)
  if aux_isZeroT dops r then none else some (i, r)

/-- Handles `enclosure`: a zonotope enclosing `Z` whose error box is folded into extra generators,
so the error is exactly `[0, 0]`. -/
def handleEnclosure (dops : DtypeOps 𝕋) (req : Json) :
    Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let n := dz.n
  let Zp := (Zonotope.absorbError dz.Z).materialise
  let h' := Zp.h
  let newCols : Array (Fin n × 𝕋) := (List.finRange n).toArray.filterMap (aux_foldRow dops Zp)
  let hFinal := h' + newCols.size
  let G : Fin hFinal → Vec 𝕋 n := fun (l : Fin hFinal) (i : Fin n) =>
    if hlt : l.val < h' then Zp.G ⟨l.val, hlt⟩ i else
      let (row, val) := newCols.getD (l.val - h') (i, FloatOps.zero)
      if row = i then val else FloatOps.zero
  let Z' : Zonotope (Vec 𝕋 n) :=
    { h := hFinal, c := Zp.c, G := G, I_error := ⟨fun _ => FloatOps.zero, fun _ => FloatOps.zero⟩ }
  pure [("Z", printZonotope dops.showExact Z')]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
