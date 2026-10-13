import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError
import CORALean.Examples.Oracle.Dtype

/-!
# `"interval"` and `"enclosure"`

`"interval"` is `Zonotope.interval`, the library's own box hull
(`Conversion/Float/Zonotope_to_Interval.lean`), sound by `Zonotope.interval_contains`.

`"enclosure"` asks for a zonotope enclosing `Z` with `E` *exactly* `[0, 0]`, for
every `Z`. `Zonotope.absorbError`, sound by `Zonotope.absorbError_outer`, moves
the box into `n` generators about its own midpoint but leaves a residual
`[lo_i, hi_i]` per row -- the rounding gap, `[0, 0]` only at a single-point box.
This folds that residual too, without rounding: each row `i` with
`[lo_i, hi_i] ≠ [0, 0]` gets one more generator `r_i · e_i`,
`r_i := maximum (neg lo_i) hi_i` -- exact, `neg`/`maximum` being exact in
every `FloatOps` -- then `E := [0, 0]`. Soundness: `e_i ∈ [lo_i, hi_i] ⊆
[-r_i, r_i]` by `r_i`'s own definition; an informal claim, as `plusBox`'s own
is, not a theorem restated here. A row already `[0, 0]` gets no generator, so
this never appends a zero one.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `x` is exactly `FloatOps.zero` -- `showExact`'s own normal form makes this a string
comparison, needing no `DecidableEq 𝕋`. -/
def aux_isZeroT (dops : DtypeOps 𝕋) (x : 𝕋) : Bool :=
  dops.showExact x = dops.showExact FloatOps.zero


-- =====================================  MAIN DEFINITION  ====================================== --

def handleInterval (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  pure [("interval", printIntervalVec dops.showExact (Zonotope.interval dz.Z))]

/-- `Zp`'s residual box, row `i`, folded into a generator radius `r_i := maximum (neg lo_i)
hi_i` -- see the module docstring for why `[lo_i,hi_i] ⊆ [-r_i,r_i]`. `none` at a row already
`[0,0]`, so a zero generator is never appended. -/
def aux_foldRow {n : ℕ} (dops : DtypeOps 𝕋) (Zp : Zonotope (Vec 𝕋 n)) (i : Fin n) :
    Option (Fin n × 𝕋) :=
  let r := FloatOps.maximum (FloatOps.neg (Zp.E.inf i)) (Zp.E.sup i)
  if aux_isZeroT dops r then none else some (i, r)

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
    { h := hFinal, c := Zp.c, G := G, E := ⟨fun _ => FloatOps.zero, fun _ => FloatOps.zero⟩ }
  pure [("Z", printZonotope dops.showExact Z')]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
