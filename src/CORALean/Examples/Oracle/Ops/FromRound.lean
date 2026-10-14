import CORALean.Examples.Oracle.Dtype
import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

/-!
# `"from"` and `"roundTo"`

`"from"` is a checked read-back: every entry must already be exactly
representable, `parseMatDyn`'s own rule, and the answer is that matrix,
normalised. `"roundTo"` is the one op whose input need not be -- `x` (a matrix)
or `Z` (a zonotope), told apart by which field is present.

The zonotope form rounds `c` and `G` entrywise by `mode`, then grows `E`
outward regardless of `mode`, `Z`'s own (still off-grid) box rounded down at
`inf` and up at `sup`. `c`'s rounding error is a fixed offset and adds
asymmetrically as before, but `G`'s is multiplied by a generator coefficient
`β ∈ [-1,1]`, so it must enter `E` *symmetrically*: a single `β` hits every
generator's own worst-case sign at once, so row `i`'s bound is one sum of
magnitudes, `r_i := sumUp_l (maximum (neg lo_il) hi_il)`, subtracted from
`E.inf` and added to `E.sup` -- not a separate `sumDown` into `E.inf` and
`sumUp` into `E.sup`, which only ever grows one side and misses exactly the
`β` that hits every generator's worst sign together. `construct Z ⊆ construct
Z'` is an informal claim, not a theorem restated here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float CORALean.Bench FloatOps
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `mode` applied to every entry of `data`, the field name of `data[i]` on failure. -/
def aux_roundArray (dops : DtypeOps 𝕋) (mode field : String) (data : Array ExactScalar) :
    Except String (Array (𝕋 × 𝕋 × 𝕋)) :=
  data.mapIdxM fun i d => match dops.roundToScalar mode d with
    | .ok t => pure t
    | .error e => throw s!"{field}[{i}]: {e}"

/-- `d`, rounded outward: `"down"` at a lower bound, `"up"` at an upper one -- `E`'s own
still-off-grid box gets this rather than `mode`, whatever `mode` the request asked for the
point values. -/
def aux_roundOutward (dops : DtypeOps 𝕋) (dir : String) (field : String) (d : ExactScalar) :
    Except String 𝕋 :=
  match dops.roundToScalar dir d with
  | .ok t => pure t.1
  | .error e => throw s!"{field}: {e}"


-- =====================================  MAIN DEFINITION  ====================================== --

def handleFrom (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let dm ← parseMatDyn dops.readExact (← field req "x")
  pure [("value", printMat dops.showExact dm.M)]

/-- `"roundTo"` at `x : Mat` -- `value` and `error` of the same shape as `x`. -/
def handleRoundToMat (dops : DtypeOps 𝕋) (mode : String) (req : Json) :
    Except String (List (String × Json)) := do
  let dm ← parseMatScalarDyn (← field req "x")
  let triples ← aux_roundArray dops mode "x.data" dm.data
  let mk (get : 𝕋 × 𝕋 × 𝕋 → 𝕋) : Mat 𝕋 dm.r dm.c :=
    Matrix.of fun (i : Fin dm.r) (l : Fin dm.c) =>
      get (triples.getD (i.val * dm.c + l.val) (FloatOps.zero, FloatOps.zero, FloatOps.zero))
  pure
    [ ("value", printMat dops.showExact (mk (·.1))),
      ("error", printIntervalMat dops.showExact ⟨mk (·.2.1), mk (·.2.2)⟩) ]

/-- `"roundTo"` at `Z : Zonotope` -- see the module docstring for why the result soundly
encloses `Z` at every `mode`. -/
def handleRoundToZonotope (dops : DtypeOps 𝕋) (mode : String) (req : Json) :
    Except String (List (String × Json)) := do
  let dz ← parseZonotopeScalar (← field req "Z")
  let n := dz.n
  let h := dz.h
  let cT ← aux_roundArray dops mode "c" dz.c
  let gT ← aux_roundArray dops mode "G" dz.G
  let eInf ← dz.Einf.mapIdxM fun i d => aux_roundOutward dops "down" s!"E.inf[{i}]" d
  let eSup ← dz.Esup.mapIdxM fun i d => aux_roundOutward dops "up" s!"E.sup[{i}]" d
  let d0 : 𝕋 × 𝕋 × 𝕋 := (FloatOps.zero, FloatOps.zero, FloatOps.zero)
  -- `G`'s row error enters `E` symmetrically -- see the module docstring for why
  let gRowBound (i : Fin n) : 𝕋 :=
    sumUp fun l : Fin h =>
      let gErr := gT.getD (i.val * h + l.val) d0
      FloatOps.maximum (FloatOps.neg gErr.2.1) gErr.2.2
  let Z : Zonotope (Vec 𝕋 n) :=
    { h := h
      c := fun i => (cT.getD i.val d0).1
      G := fun (l : Fin h) (i : Fin n) => (gT.getD (i.val * h + l.val) d0).1
      I_error := ⟨fun i => subDown (addDown (eInf.getD i.val FloatOps.zero) (cT.getD i.val d0).2.1)
              (gRowBound i),
            fun i => addUp (addUp (eSup.getD i.val FloatOps.zero) (cT.getD i.val d0).2.2)
              (gRowBound i)⟩ }
  pure [("Z", printZonotope dops.showExact Z)]

/-- `"roundTo"`, told apart by which of `x`/`Z` the request carries. -/
def handleRoundTo (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  let mode ← strField req "mode"
  match fieldOpt req "Z", fieldOpt req "x" with
  | some _, _ => handleRoundToZonotope dops mode req
  | none, some _ => handleRoundToMat dops mode req
  | none, none => throw "roundTo: needs either `x` (a matrix) or `Z` (a zonotope)"

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
